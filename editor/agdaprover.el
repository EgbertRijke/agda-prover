;;; agdaprover.el --- AgdaProver integration for agda-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Egbert Rijke and contributors
;; SPDX-License-Identifier: GPL-3.0-or-later
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.
;;
;; Version: 0.0.1
;; Package-Requires: ((emacs "27.1"))
;; Keywords: languages, tools, agda
;; URL: https://github.com/EgbertRijke/agda-prover

;;; Commentary:

;; Run the local AgdaProver P0 CLI asynchronously from an agda-mode goal.
;; A returned single- or multi-goal proof is applied through agda-mode only
;; after AgdaProver reports fresh-process validation and the source buffer still
;; matches the snapshot used to run proof search.  One-step actions are accepted
;; by AgdaProver's
;; Agda session, then replayed through agda-mode's refinement command so that
;; every new subgoal remains interactive.

;;; Code:

(require 'cl-lib)
(require 'easymenu)
(require 'json)
(require 'subr-x)
(require 'agda2-mode)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lagda\\.md\\'" . agda2-mode))

(defgroup agdaprover nil
  "Local AgdaProver integration for agda-mode."
  :group 'agda2
  :prefix "agdaprover-")

(defconst agdaprover--default-project-root
  (file-name-as-directory
   (expand-file-name
    ".."
    (file-name-directory (or load-file-name buffer-file-name default-directory))))
  "Repository root inferred from the location of this package.")

(defcustom agdaprover-project-root agdaprover--default-project-root
  "Root of the AgdaProver checkout containing the `src' directory."
  :type 'directory
  :group 'agdaprover)

(defcustom agdaprover-python-command "python3"
  "Python executable used to launch the AgdaProver module."
  :type 'string
  :group 'agdaprover)

(defcustom agdaprover-agda-executable nil
  "Optional Agda compiler executable.  Nil uses agda from PATH."
  :type '(choice (const nil) string)
  :group 'agdaprover)

(defcustom agdaprover-library-file nil
  "Explicit Agda library registry.  Ambient default libraries are never used."
  :type '(choice (const nil) file)
  :group 'agdaprover)

(defcustom agdaprover-agda-options nil
  "Global Agda checking options, or nil for --without-K and --exact-split.
An empty vector supplies no global options.  These do not replace the
separate library and source-file flags."
  :type '(choice (const nil) (const :tag "No global options" []) (repeat string))
  :group 'agdaprover)

(make-variable-buffer-local 'agdaprover-agda-executable)
(make-variable-buffer-local 'agdaprover-library-file)
(make-variable-buffer-local 'agdaprover-agda-options)

(defun agdaprover--project-configuration ()
  "Return explicit checking configuration, or nil for legacy defaults."
  (when (or agdaprover-agda-executable agdaprover-library-file agdaprover-agda-options)
    `((schema_version . "agdaprover.project-configuration.v1")
      (executable . ,(if (and agdaprover-agda-executable
                             (string-match-p "/" agdaprover-agda-executable))
                        (expand-file-name agdaprover-agda-executable)
                      (or agdaprover-agda-executable "agda")))
      (library_file . ,(if agdaprover-library-file
                          (expand-file-name agdaprover-library-file) :null))
      (options . ,(vconcat (or agdaprover-agda-options '("--without-K" "--exact-split")))))))

(defcustom agdaprover-ranker 'auto
  "Candidate ranker used by `agdaprover-prove-goal'.

`auto' and `nnue' use the bundled NNUE models unless overridden.
`symbolic' disables neural ranking."
  :type '(choice (const :tag "Bundled NNUE defaults" auto)
                 (const :tag "Deterministic symbolic" symbolic)
                 (const :tag "NNUE" nnue))
  :group 'agdaprover)

(defcustom agdaprover-step-ranker nil
  "Candidate ranker used by `agdaprover-step-goal'.

When nil, one-step search follows `agdaprover-ranker'."
  :type '(choice (const :tag "Follow the proof ranker" nil)
                 (const :tag "Deterministic symbolic" symbolic)
                 (const :tag "One-step NNUE" nnue))
  :group 'agdaprover)

(defcustom agdaprover-model-file nil
  "Override the bundled proof/focused-branch NNUE model, or nil for the default."
  :type '(choice (const :tag "Use bundled model" nil) file)
  :group 'agdaprover)

(defcustom agdaprover-step-model-file nil
  "NNUE model trained for one-step refinement ranking.

When nil, NNUE one-step ranking uses the bundled one-step model.
Overrides must have the `one-step-refinement-ranking' role."
  :type '(choice (const :tag "Use bundled one-step model" nil) file)
  :group 'agdaprover)

(defcustom agdaprover-action-model-file nil
  "NNUE model trained for shared solver OR-decision ranking.

When nil, use the bundled OR policy.  This model is used only by complete
proof and joint-prefix search with NNUE ranking.
It must have the `or-decision-ranking' role.  In particular, a
`one-step-refinement-ranking' model belongs in
`agdaprover-step-model-file', not here."
  :type '(choice (const :tag "Use bundled OR policy" nil) file)
  :group 'agdaprover)

(defcustom agdaprover-search-profile 'standard
  "Search effort preset: `standard' (500 actions) or `deep' (8000 actions).
Explicit limits override preset values.
Neither preset adds a time or depth cap."
  :type '(choice (const standard) (const deep))
  :group 'agdaprover)

(defcustom agdaprover-max-candidates nil
  "Whole-run action allowance, or nil to use the search profile's default.
This counts search actions, not physical Agda calls."
  :type '(choice (const :tag "Use search profile" nil) integer)
  :group 'agdaprover)

(defcustom agdaprover-max-term-size 8
  "Maximum P0 term-IR size for one proof search."
  :type 'integer
  :group 'agdaprover)

(defcustom agdaprover-max-depth nil
  "Optional hard proof-search depth, or nil for no explicit depth bound.

The action budget and any separately configured wall-time limit remain active
when this is nil."
  :type '(choice (const :tag "No explicit depth bound" nil) integer)
  :group 'agdaprover)

(defcustom agdaprover-timeout nil
  "Optional wall-time limit in seconds, or nil for no wall-time limit."
  :type '(choice (const :tag "No wall-time limit" nil) number)
  :group 'agdaprover)

(defcustom agdaprover-apply-policy 'ask
  "How to handle a fresh-validated proof returned for an unchanged goal.

`ask' prompts before applying it through agda-mode.  `always' applies it
without prompting.  `never' only records and displays the result."
  :type '(choice (const ask) (const always) (const never))
  :group 'agdaprover)

(defvar-local agdaprover--process nil
  "The active AgdaProver process for the current source buffer.")

(defvar-local agdaprover--last-result nil
  "The most recent parsed AgdaProver result for the current buffer.")

(defvar-local agdaprover--last-step-result nil
  "The most recent one-step result for the current buffer.")

(defvar-local agdaprover--last-goal-id nil)
(defvar-local agdaprover--last-source-tick nil)
(defvar-local agdaprover--last-goal-marker nil)
(defvar-local agdaprover--last-output-buffer nil)
(defvar-local agdaprover--entry-report-process nil
  "Process currently owning this entry-test report buffer.")

(defun agdaprover--project-root ()
  "Return the normalized configured AgdaProver repository root."
  (file-name-as-directory (expand-file-name agdaprover-project-root)))

(defun agdaprover--pythonpath ()
  "Return the source directory needed to import AgdaProver."
  (expand-file-name "src" (agdaprover--project-root)))

(defun agdaprover--validate-configuration (ranker model-file)
  "Signal a user error if RANKER and MODEL-FILE cannot run."
  (unless (file-directory-p (agdaprover--pythonpath))
    (user-error "AgdaProver src directory not found under %s"
                (agdaprover--project-root)))
  (unless (executable-find agdaprover-python-command)
    (user-error "Python executable not found: %s" agdaprover-python-command))
  (when (and (eq ranker 'nnue) model-file)
    (unless (file-readable-p model-file)
      (user-error "Select a readable NNUE model for this operation"))))

(defun agdaprover--resolve-ranker (ranker _model-file)
  "Resolve RANKER to `nnue' or `symbolic'.

The backend supplies operation-specific bundled models when none is selected."
  (if (eq ranker 'auto)
      'nnue
    ranker))

(defun agdaprover--action-model-for-operation (operation)
  "Return the role-compatible optional action model for OPERATION."
  (when (memq operation '(prove prove-prefix test-entries))
    agdaprover-action-model-file))

(defun agdaprover--search-command
    (operation source-file goal-position ranker model-file &optional action-model-file)
  "Build an OPERATION command for SOURCE-FILE at GOAL-POSITION.

RANKER and MODEL-FILE select the candidate ordering implementation."
  (agdaprover--validate-configuration ranker model-file)
  (append
   (list agdaprover-python-command
         "-m" "agdaprover" operation
         (expand-file-name source-file)
         "--goal-position" (number-to-string goal-position)
         "--ranker" (symbol-name ranker))
   (unless (eq agdaprover-search-profile 'standard)
     (list "--search-profile" (symbol-name agdaprover-search-profile)))
   (when agdaprover-max-candidates
     (list "--max-candidates" (number-to-string agdaprover-max-candidates)))
   (list "--max-term-size" (number-to-string agdaprover-max-term-size))
   (when agdaprover-agda-executable
     (list "--agda" (alist-get 'executable (agdaprover--project-configuration))))
   (when agdaprover-library-file (list "--library-file" (expand-file-name agdaprover-library-file)))
   (mapcar (lambda (option) (concat "--agda-option=" option)) agdaprover-agda-options)
   (when (equal agdaprover-agda-options []) (list "--no-default-agda-options"))
   (when agdaprover-timeout
     (list "--timeout" (number-to-string agdaprover-timeout)))
   (when agdaprover-max-depth
     (list "--max-depth" (number-to-string agdaprover-max-depth)))
   (when (eq ranker 'nnue)
     (append
      (when model-file (list "--model" (expand-file-name model-file)))
      (when (and (member operation '("prove" "prove-prefix"))
                 action-model-file)
        (list "--action-model" (expand-file-name action-model-file)))))))

(defun agdaprover--command (source-file goal-position ranker)
  "Build a proof command for SOURCE-FILE at GOAL-POSITION using RANKER."
  (agdaprover--search-command
   "prove" source-file goal-position ranker agdaprover-model-file
   (agdaprover--action-model-for-operation 'prove)))

(defun agdaprover--step-command (source-file goal-position ranker)
  "Build a one-step command for SOURCE-FILE at GOAL-POSITION using RANKER."
  (agdaprover--search-command
   "step"
   source-file
   goal-position
   ranker
   agdaprover-step-model-file))

(defun agdaprover--prefix-command (source-file cutoff-position ranker)
  "Build a joint-prefix command through CUTOFF-POSITION using RANKER."
  (agdaprover--search-command
   "prove-prefix" source-file cutoff-position ranker agdaprover-model-file
   (agdaprover--action-model-for-operation 'prove-prefix)))

(defun agdaprover--editor-command (ranker model-file)
  "Build the universal editor API command for RANKER and MODEL-FILE."
  (agdaprover--validate-configuration ranker model-file)
  (list agdaprover-python-command "-m" "agdaprover" "editor-api"))

(defun agdaprover--editor-request
    (request-id operation source-file goal-position ranker model-file
                &optional action-model-file)
  "Build one versioned editor request.

REQUEST-ID correlates the response.  OPERATION, SOURCE-FILE, GOAL-POSITION,
RANKER, MODEL-FILE, and ACTION-MODEL-FILE have the same meaning for every
editor client."
  (let ((source-sha256
         (with-temp-buffer
           (insert-file-contents-literally source-file)
           (secure-hash 'sha256 (current-buffer)))))
    `((schema_version . "agdaprover.editor.request.v1")
      (request_id . ,request-id)
      (operation . ,(symbol-name operation))
      (source_file . ,(expand-file-name source-file))
      (source_sha256 . ,source-sha256)
      (goal_position . ,goal-position)
      (ranker . ,(symbol-name ranker))
      (model . ,(or (and (eq ranker 'nnue)
                         model-file
                         (expand-file-name model-file))
                    :null))
      (action_model . ,(or (and (eq ranker 'nnue)
                                action-model-file
                                (expand-file-name action-model-file))
                           :null))
      ,@(unless (eq agdaprover-search-profile 'standard)
          `((search_profile . ,(symbol-name agdaprover-search-profile))))
      ,@(when agdaprover-max-candidates
          `((max_candidates . ,agdaprover-max-candidates)))
      (max_term_size . ,agdaprover-max-term-size)
      (max_depth . ,(or agdaprover-max-depth :null))
      (timeout_seconds . ,(or agdaprover-timeout :null))
      ,@(when-let* ((configuration (agdaprover--project-configuration)))
          `((project_configuration . ,configuration))))))

(defun agdaprover--goal-at-point ()
  "Return the agda-mode goal number at point or signal a user error."
  (unless (derived-mode-p 'agda2-mode)
    (user-error "AgdaProver commands must run in an agda-mode buffer"))
  (let ((goal (agda2-goal-at (point))))
    (unless (and goal (cadr goal))
      (user-error "Point is not inside an agda-mode goal"))
    (cadr goal)))

(defun agdaprover--goal-source-position (goal-id)
  "Return Agda's one-based source position for GOAL-ID."
  (let ((overlay (agda2-goal-overlay goal-id)))
    (unless overlay
      (user-error "agda-mode goal %s is no longer present" goal-id))
    (overlay-start overlay)))

(defun agdaprover--open-goal-overlays ()
  "Return all agda-mode goal overlays in source order."
  (sort
   (cl-remove-if-not
    (lambda (overlay) (overlay-get overlay 'agda2-gn))
    (overlays-in (point-min) (point-max)))
   (lambda (left right) (< (overlay-start left) (overlay-start right)))))

(defun agdaprover--joint-prefix-selection ()
  "Select a goal prefix when point is in a goal, otherwise all goals.

Return (FIRST-ID SELECTION-POSITION COUNT), and move point to the first selected
goal.  A goal containing point is the inclusive cutoff.  Point anywhere else
selects every open goal in the file."
  (unless (derived-mode-p 'agda2-mode)
    (user-error "AgdaProver commands must run in an agda-mode buffer"))
  (let* ((cursor (point))
         (goals (agdaprover--open-goal-overlays))
         (cutoff
          (cl-find-if
           (lambda (overlay)
             (and (<= (overlay-start overlay) cursor)
                  (< cursor (overlay-end overlay))))
           goals)))
    (unless goals
      (user-error "No open agda-mode goals; load the buffer with C-c C-l"))
    (let* ((selected
            (if cutoff
                (cl-loop for overlay in goals
                         collect overlay
                         until (eq overlay cutoff))
              goals))
           (first (car selected))
           (first-id (overlay-get first 'agda2-gn))
           (selection-position
            (if cutoff (overlay-start cutoff) cursor)))
      (agda2-goto-goal first-id)
      (list first-id selection-position (length selected)))))

(defun agdaprover--prefix-progress-target (selection-position)
  "Describe the joint-prefix target selected at SELECTION-POSITION.

When the position is inside an open goal, name that inclusive cutoff goal.
Otherwise report that every open goal is selected.  This is intentionally
independent of the first selected goal, which remains the stale-snapshot and
patch-application anchor."
  (let* ((goals (agdaprover--open-goal-overlays))
         (cutoff
          (cl-find-if
           (lambda (overlay)
             (and (<= (overlay-start overlay) selection-position)
                  (< selection-position (overlay-end overlay))))
           goals)))
    (if cutoff
        (let ((count (1+ (cl-position cutoff goals :test #'eq))))
          (format "through goal %s (%d selected goal%s)"
                  (overlay-get cutoff 'agda2-gn)
                  count
                  (if (= count 1) "" "s")))
      (format "all %d open goal%s"
              (length goals)
              (if (= (length goals) 1) "" "s")))))

(defun agdaprover--process-environment ()
  "Return a local process environment that can import AgdaProver."
  (let* ((separator (if (characterp path-separator)
                        (char-to-string path-separator)
                      path-separator))
         (existing (getenv "PYTHONPATH"))
         (pythonpath (if (and existing (not (string-empty-p existing)))
                         (concat (agdaprover--pythonpath) separator existing)
                       (agdaprover--pythonpath))))
    (let ((process-environment (copy-sequence process-environment)))
      (setenv "PYTHONPATH" pythonpath)
      process-environment)))

(defun agdaprover--prepare-process-buffer (name)
  "Create and clear a read-only process buffer named NAME."
  (let ((buffer (get-buffer-create name)))
    (with-current-buffer buffer
      (let ((inhibit-read-only t))
        (erase-buffer))
      (special-mode))
    buffer))

(defun agdaprover--process-filter (process text)
  "Append TEXT from PROCESS to its output buffer."
  (when (eq (process-get process 'agdaprover-operation) 'test-entries)
    (agdaprover--entry-test-filter process text))
  (when-let* ((buffer (process-buffer process)))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (let ((inhibit-read-only t))
          (goto-char (point-max))
          (insert text))))))

(defun agdaprover--parse-json-buffer (buffer)
  "Parse one AgdaProver JSON object from BUFFER."
  (unless (buffer-live-p buffer)
    (error "AgdaProver output buffer was deleted"))
  (with-current-buffer buffer
    (goto-char (point-min))
    (json-parse-buffer
     :object-type 'alist
     :array-type 'list
     :null-object nil
     :false-object nil)))

(defun agdaprover--buffer-snapshot-current-p (buffer tick goal-id marker)
  "Return non-nil if BUFFER still matches TICK and contains GOAL-ID at MARKER."
  (and (buffer-live-p buffer)
       (marker-position marker)
       (with-current-buffer buffer
         (and (= tick (buffer-chars-modified-tick))
              (when-let* ((overlay (agda2-goal-overlay goal-id)))
                (let ((position (marker-position marker)))
                  (and (<= (overlay-start overlay) position)
                       (< position (overlay-end overlay)))))))))

(defun agdaprover--first-diagnostic (result)
  "Extract the first diagnostic message from RESULT."
  (or (when-let* ((diagnostics (alist-get 'diagnostics result))
                  (first (car diagnostics)))
        (alist-get 'message first))
      (alist-get 'diagnostic result)))

(defun agdaprover--verified-result-well-formed-p (result)
  "Return non-nil when RESULT carries the minimum verified-result evidence."
  (let ((proof (alist-get 'proof_term result))
        (patch (alist-get 'patch result))
        (validation (alist-get 'validation result))
        (trust-report (alist-get 'trust_report result)))
    (and (equal (alist-get 'schema_version result) "agdaprover.p0.v1")
         (equal (alist-get 'status result) "verified")
         (stringp proof)
         (not (string-empty-p proof))
         (listp patch)
         (equal (alist-get 'schema_version patch)
                "agdaprover.reconstruction.p0.v1")
         (listp validation)
         (alist-get 'checked validation)
         (listp trust-report)
         trust-report)))

(defun agdaprover--source-hole-p (text)
  "Return non-nil when TEXT is one complete Agda interaction hole."
  (and (stringp text)
       (or (equal text "?")
           (and (string-prefix-p "{!" text)
                (string-suffix-p "!}" text)))))

(defun agdaprover--valid-clause-binder-p (binder)
  "Return non-nil when BINDER is safe in a reconstructed clause head."
  (and (stringp binder)
       (not (string-empty-p binder))
       (not (member binder '("λ" "→" "?")))
       (not (string-match-p "[[:space:]=]" binder))))

(defun agdaprover--formatter-metadata-p (metadata)
  "Return non-nil when METADATA is one supported proof-formatter record."
  (let ((digest-pattern "\\`[[:xdigit:]]\\{64\\}\\'"))
    (and (listp metadata)
         (= (length metadata) 8)
         (equal (alist-get 'schema_version metadata)
                "agdaprover.proof-formatter.v1")
         (equal (alist-get 'profile metadata) "agda-unimath-v1")
         (equal (alist-get 'scope metadata) "generated-proof-term")
         (member (alist-get 'status metadata)
                 '("formatted" "preserved-unsupported"))
         (assq 'changed metadata)
         (or (eq (alist-get 'changed metadata) t)
             (null (alist-get 'changed metadata)))
         (integerp (alist-get 'line_width metadata))
         (> (alist-get 'line_width metadata) 0)
         (string-match-p digest-pattern
                         (or (alist-get 'input_sha256 metadata) ""))
         (string-match-p digest-pattern
                         (or (alist-get 'output_sha256 metadata) "")))))

(defun agdaprover--joint-step-shape-p (step)
  "Return non-nil when structured joint STEP reconstructs its replacement."
  (let* ((style (alist-get 'style step))
         (original (alist-get 'original step))
         (replacement (alist-get 'replacement step))
         (binders (alist-get 'binders step))
         (body (alist-get 'body step))
         (formatter (alist-get 'formatter step))
         (layout (or (alist-get 'layout step) "inline"))
         (equals (and (stringp original) (cl-position ?= original :from-end t)))
         (lhs (and equals (string-trim-right (substring original 0 equals))))
         (hole (and equals (string-trim (substring original (1+ equals))))))
    (and (equal (alist-get 'schema_version step)
                "agdaprover.reconstruction.p0.v1")
         (listp binders)
         (cl-every #'agdaprover--valid-clause-binder-p binders)
         (stringp body)
         (or (not (assq 'formatter step))
             (agdaprover--formatter-metadata-p formatter))
         (pcase style
           ("term"
            (and (null binders)
                 (agdaprover--source-hole-p original)
                 (equal replacement body)))
           ("case-split"
            (and (null binders)
                 (equal replacement body)
                 (or (string-match-p "{!" original)
                     (string-match-p (regexp-quote "?") original))))
           ("guided-clauses"
            (and (null binders)
                 (equal replacement body)
                 (agdaprover--source-hole-p hole)))
           ((or "clause" "clause-intro")
            (let* ((expected-body
                    (if (equal style "clause-intro") hole body))
                   (leading
                    (and (stringp lhs)
                         (string-match "\\`[ \t]*" lhs)
                         (match-string 0 lhs)))
                   (continuation
                    (make-string (+ (string-width (or leading "")) 2) ?\s))
                   (expected
                    (cond
                     ((equal layout "inline")
                      (format "%s %s = %s"
                              lhs (string-join binders " ") expected-body))
                     ((and (equal layout "next-line")
                           (equal style "clause"))
                      (format "%s %s =\n%s%s"
                              lhs (string-join binders " ")
                              continuation expected-body)))))
              (and binders
                   (stringp lhs)
                   (not (string-empty-p lhs))
                   (agdaprover--source-hole-p hole)
                   (stringp expected)
                   (equal replacement expected))))
           (_ nil)))))

(defun agdaprover--replay-joint-step (source step joint-start)
  "Replay structured STEP in SOURCE relative to one-based JOINT-START."
  (let* ((source-range (alist-get 'source_range step))
         (start (car-safe source-range))
         (end (cadr source-range))
         (original (alist-get 'original step))
         (replacement (alist-get 'replacement step))
         (local-start (and (integerp start) (- start joint-start)))
         (local-end (and (integerp end) (- end joint-start))))
    (unless (and (agdaprover--joint-step-shape-p step)
                 (integerp local-start)
                 (integerp local-end)
                 (<= 0 local-start)
                 (< local-start local-end)
                 (<= local-end (length source))
                 (stringp original)
                 (stringp replacement)
                 (equal (substring source local-start local-end) original))
      (user-error "Malformed AgdaProver joint edit trace"))
    (concat (substring source 0 local-start)
            replacement
            (substring source local-end))))

(defun agdaprover--apply-source-edit (edit)
  "Apply a validated reconstruction EDIT and reload the Agda buffer."
  (unless (equal (alist-get 'schema_version edit)
                 "agdaprover.reconstruction.p0.v1")
    (user-error "Unsupported AgdaProver reconstruction version"))
  (let* ((source-range (alist-get 'source_range edit))
         (start (car-safe source-range))
         (end (cadr source-range))
         (style (alist-get 'style edit))
         (original (alist-get 'original edit))
         (replacement (alist-get 'replacement edit)))
    (unless (and (integerp start)
                 (integerp end)
                 (< 0 start end)
                 (<= end (1+ (point-max)))
                 (member style '("term" "clause" "clause-intro" "case-split"
                                 "guided-clauses" "joint-clauses"))
                 (stringp original)
                 (stringp replacement))
      (user-error "Malformed AgdaProver reconstruction edit"))
    (when (assq 'formatter edit)
      (unless (agdaprover--formatter-metadata-p
               (alist-get 'formatter edit))
        (user-error "Malformed AgdaProver formatter metadata")))
    (when (equal style "joint-clauses")
      (let ((count (alist-get 'target_goal_count edit))
            (cutoff (alist-get 'cutoff_position edit))
            (steps (alist-get 'steps edit)))
        (unless (and (integerp count)
                     (> count 0)
                     (integerp cutoff)
                     (<= start cutoff)
                     (< cutoff end)
                     (listp steps)
                     steps)
          (user-error "Malformed AgdaProver joint reconstruction"))
        (let ((replayed original))
          (dolist (step steps)
            (setq replayed
                  (agdaprover--replay-joint-step replayed step start)))
          (unless (equal replayed replacement)
            (user-error "Joint patch does not match its structured edit trace")))))
    (unless (equal (buffer-substring-no-properties start end) original)
      (user-error "The declaration changed; refusing a stale reconstruction edit"))
    (atomic-change-group
      (goto-char start)
      (delete-region start end)
      (insert replacement))
    (agda2-load)))

(defun agdaprover--apply-result (result goal-id)
  "Apply the verified proof in RESULT to GOAL-ID through agda-mode."
  (unless (agdaprover--verified-result-well-formed-p result)
    (user-error "AgdaProver result lacks fresh validation evidence"))
  (let* ((proof (alist-get 'proof_term result))
         (patch (alist-get 'patch result))
         (style (and patch (alist-get 'style patch))))
    (unless (and (stringp proof) (not (string-empty-p proof)))
      (user-error "The last AgdaProver result contains no proof term"))
    (when (bound-and-true-p agda2-in-progress)
      (user-error "agda-mode is busy; apply the proof after it becomes idle"))
    (unless (agda2-goal-overlay goal-id)
      (user-error "agda-mode goal %s is no longer present" goal-id))
    (when (equal style "joint-clauses")
      (let ((count (alist-get 'target_goal_count patch)))
        (unless (and (integerp count)
                     (= count (length (alist-get 'joint_goals result))))
          (user-error "Joint result goal count does not match its patch"))))
    (if (member style '("clause" "guided-clauses" "joint-clauses"))
        (agdaprover--apply-source-edit patch)
      (agda2-replace-goal goal-id proof)
      (agda2-goto-goal goal-id)
      (agda2-give nil))))

(defun agdaprover--apply-step-result (result goal-id)
  "Replay the Agda-accepted refinement in RESULT at GOAL-ID."
  (let* ((action (alist-get 'action result))
         (expression (alist-get 'expression action))
         (source-edit (alist-get 'source_edit action)))
    (unless (stringp expression)
      (user-error "The one-step result contains no refinement expression"))
    (when (bound-and-true-p agda2-in-progress)
      (user-error "agda-mode is busy; retry the step after it becomes idle"))
    (unless (agda2-goal-overlay goal-id)
      (user-error "agda-mode goal %s is no longer present" goal-id))
    (if source-edit
        (agdaprover--apply-source-edit source-edit)
      (agda2-replace-goal goal-id expression)
      (agda2-goto-goal goal-id)
      (agda2-refine nil))))

(defun agdaprover--offer-result (source-buffer result tick goal-id marker output-buffer)
  "Store and optionally apply RESULT in SOURCE-BUFFER.

TICK, GOAL-ID, and MARKER identify the source snapshot.  OUTPUT-BUFFER holds
the complete machine-readable result."
  (if (not (buffer-live-p source-buffer))
      (display-buffer output-buffer)
    (with-current-buffer source-buffer
      (setq agdaprover--last-result result
            agdaprover--last-goal-id goal-id
            agdaprover--last-source-tick tick
            agdaprover--last-goal-marker marker
            agdaprover--last-output-buffer output-buffer)
      (let ((status (alist-get 'status result)))
        (cond
         ((equal status "impossible")
          ;; Keep the replayable certificate in the last-result buffer, but do
          ;; not cover the source with a large JSON window for this expected
          ;; logical outcome.
          (message "AgdaProver: %s"
                   (or (agdaprover--first-diagnostic result)
                       "This goal is impossible; Agda checked its refutation.")))
         ((not (equal status "verified"))
            (progn
              (message "AgdaProver: %s%s"
                       status
                       (if-let* ((diagnostic (agdaprover--first-diagnostic result)))
                           (format " — %s" diagnostic)
                         ""))
              (display-buffer output-buffer)))
         ((not (agdaprover--verified-result-well-formed-p result))
          (message "AgdaProver returned malformed verification evidence; result not applied")
          (display-buffer output-buffer))
         (t
          (let* ((proof (alist-get 'proof_term result))
                 (joint-count (length (alist-get 'joint_goals result)))
                 (description
                  (if (> joint-count 1)
                      (format "%d jointly constrained goals" joint-count)
                    (format "`%s'" proof)))
                 (apply-pronoun (if (> joint-count 1) "them" "it")))
            (cond
             ((not (agdaprover--buffer-snapshot-current-p
                    source-buffer tick goal-id marker))
              (message "AgdaProver verified %s, but the goal buffer changed; result not applied"
                       description)
              (display-buffer output-buffer))
             ((eq agdaprover-apply-policy 'always)
              (agdaprover--apply-result result goal-id))
             ((and (eq agdaprover-apply-policy 'ask)
                   (y-or-n-p
                    (format "AgdaProver verified %s. Apply %s? "
                            description apply-pronoun)))
              (agdaprover--apply-result result goal-id))
             (t
              (message "AgdaProver verified %s; use M-x agdaprover-apply-last-proof"
                       description)
              (display-buffer output-buffer))))))))))

(defun agdaprover--offer-step
    (source-buffer result tick goal-id marker output-buffer)
  "Apply an accepted one-step RESULT to an unchanged SOURCE-BUFFER.

TICK, GOAL-ID, and MARKER identify the source snapshot. OUTPUT-BUFFER contains
the complete machine-readable action result."
  (if (not (buffer-live-p source-buffer))
      (display-buffer output-buffer)
    (with-current-buffer source-buffer
      (setq agdaprover--last-step-result result
            agdaprover--last-output-buffer output-buffer)
      (let ((status (alist-get 'status result)))
        (cond
         ((not (equal status "accepted-step"))
          (message "AgdaProver step: %s%s"
                   status
                   (if-let* ((diagnostic (agdaprover--first-diagnostic result)))
                       (format " — %s" diagnostic)
                     ""))
          (display-buffer output-buffer))
         ((not (agdaprover--buffer-snapshot-current-p
                source-buffer tick goal-id marker))
          (message "AgdaProver found a step, but the goal buffer changed; step not applied")
          (display-buffer output-buffer))
         (t
          (let* ((action (alist-get 'action result))
                 (hint (alist-get 'reconstruction_hint action)))
            (message "AgdaProver: refining with %s" hint)
            (agdaprover--apply-step-result result goal-id))))))))

(defun agdaprover--sentinel (process event)
  "Handle termination of AgdaProver PROCESS described by EVENT."
  (when (and (memq (process-status process) '(exit signal))
             (not (process-get process 'agdaprover-finished)))
    (process-put process 'agdaprover-finished t)
    (let* ((source-buffer (process-get process 'agdaprover-source-buffer))
           (output-buffer (process-buffer process))
           (stderr-buffer (process-get process 'agdaprover-stderr-buffer))
           (tick (process-get process 'agdaprover-source-tick))
           (goal-id (process-get process 'agdaprover-goal-id))
           (marker (process-get process 'agdaprover-goal-marker))
           (owns-source
            (and (buffer-live-p source-buffer)
                 (with-current-buffer source-buffer
                   (eq agdaprover--process process)))))
      (when (buffer-live-p source-buffer)
        (with-current-buffer source-buffer
          (when owns-source
            (setq agdaprover--process nil))))
      (cond
       ((and owns-source (eq (process-get process 'agdaprover-operation) 'test-entries))
        (unless (process-get process 'agdaprover-entry-final)
          (agdaprover--entry-test-append
           process "\n%s\n"
           (or (process-get process 'agdaprover-entry-error)
               (and (process-get process 'agdaprover-cancelled) "Entry testing cancelled.")
               (format "Entry testing stopped unexpectedly (%s). See the error buffer."
                       (string-trim event)))))
        (when (and (not (process-get process 'agdaprover-entry-final))
                   (buffer-live-p stderr-buffer)
                   (> (buffer-size stderr-buffer) 0))
          (display-buffer stderr-buffer)))
       ((process-get process 'agdaprover-cancelled)
        (message "AgdaProver search cancelled"))
       ((and (buffer-live-p source-buffer) (not owns-source))
        ;; A new command may start after this process exits but before Emacs
        ;; dispatches its sentinel.  The old result no longer owns the source
        ;; buffer and must never overwrite or apply the newer command's state.
        (message "AgdaProver ignored a superseded process result"))
       (t
        (condition-case error-data
            (let* ((envelope (agdaprover--parse-json-buffer output-buffer))
                   (expected-id (process-get process 'agdaprover-request-id))
                   (result
                    (if (equal (alist-get 'schema_version envelope)
                               "agdaprover.editor.response.v1")
                        (progn
                          (unless (equal (alist-get 'request_id envelope)
                                         expected-id)
                            (error "AgdaProver editor response ID mismatch"))
                          (alist-get 'result envelope))
                      ;; Accept the old direct CLI shape only for a bounded
                      ;; transition period when inspecting saved output.
                      envelope)))
              (if (eq (process-get process 'agdaprover-operation) 'step)
                  (agdaprover--offer-step
                   source-buffer result tick goal-id marker output-buffer)
                (agdaprover--offer-result
                 source-buffer result tick goal-id marker output-buffer)))
          (error
           (message "AgdaProver process failed (%s): %s"
                    (string-trim event)
                    (error-message-string error-data))
           (display-buffer output-buffer)
           (when (and (buffer-live-p stderr-buffer)
                      (> (buffer-size stderr-buffer) 0))
             (display-buffer stderr-buffer)))))))))

(defun agdaprover--start-operation
    (operation ranker &optional selected-goal-id selected-goal-position)
  "Start asynchronous OPERATION using RANKER.

SELECTED-GOAL-ID and SELECTED-GOAL-POSITION let a joint-prefix command keep
the first goal as its stale-snapshot anchor while passing a later cutoff."
  (let* ((model-file
          (if (eq operation 'step)
              agdaprover-step-model-file
            agdaprover-model-file))
         (action-model-file
          (agdaprover--action-model-for-operation operation))
         (ranker (agdaprover--resolve-ranker ranker model-file))
         (goal-id (unless (eq operation 'test-entries)
                    (or selected-goal-id (agdaprover--goal-at-point)))))
    (unless buffer-file-name
      (user-error "The current Agda buffer is not visiting a file"))
    (when (process-live-p agdaprover--process)
      (user-error "An AgdaProver search is already running in this buffer"))
    (if (eq operation 'test-entries)
        (when (or (buffer-modified-p) (not (verify-visited-file-modtime (current-buffer))))
          (user-error "Save or revert your changes before testing; entry testing never writes this file"))
      (save-buffer))
    (let* ((goal-position
            (or (and (eq operation 'test-entries) 1) selected-goal-position
                (agdaprover--goal-source-position goal-id)))
           (source-buffer (current-buffer))
           (source-tick (buffer-chars-modified-tick))
           (goal-marker (copy-marker (point)))
           (output-buffer
            (agdaprover--prepare-process-buffer
             (format "*AgdaProver %s*" (buffer-name source-buffer))))
           (stderr-buffer
            (agdaprover--prepare-process-buffer
             (format "*AgdaProver errors %s*" (buffer-name source-buffer))))
           (default-directory (agdaprover--project-root))
           (process-environment (agdaprover--process-environment))
           (request-id
            (format "emacs:%s:%s"
                    (emacs-pid)
                    (secure-hash
                     'sha256
                     (format "%s:%s:%s"
                             buffer-file-name source-tick (float-time)))))
           (command (agdaprover--editor-command ranker model-file))
           (request
            (agdaprover--editor-request
             request-id operation buffer-file-name goal-position ranker
             model-file action-model-file))
           (process
            (make-process
             :name (format "agdaprover-%s-%s" operation (buffer-name source-buffer))
             :buffer output-buffer
             :command command
             :connection-type 'pipe
             :coding 'utf-8-unix
             :filter #'agdaprover--process-filter
             ;; Install the real sentinel only after every property below is
             ;; attached.  Focused searches can finish before `make-process'
             ;; returns on fast machines.
             :sentinel #'ignore
             :stderr stderr-buffer
             :noquery t)))
      (process-put process 'agdaprover-source-buffer source-buffer)
      (process-put process 'agdaprover-source-tick source-tick)
      (process-put process 'agdaprover-goal-id goal-id)
      (process-put process 'agdaprover-goal-marker goal-marker)
      (process-put process 'agdaprover-stderr-buffer stderr-buffer)
      (process-put process 'agdaprover-operation operation)
      (process-put process 'agdaprover-request-id request-id)
      (process-put process 'agdaprover-source-sha256 (alist-get 'source_sha256 request))
      (setq agdaprover--process process)
      (when (eq operation 'test-entries)
        (let ((report (agdaprover--prepare-process-buffer
                       (format "*AgdaProver entry tests %s*" (buffer-name source-buffer)))))
          (process-put process 'agdaprover-entry-report report)
          (with-current-buffer report
            (setq agdaprover--entry-report-process process)
            (use-local-map (copy-keymap (current-local-map)))
            (local-set-key (kbd "C-c C-x C-k")
                           (lambda () (interactive) (agdaprover--stop-process process)))
            (add-hook 'kill-buffer-hook
                      (lambda () (agdaprover--stop-process process)) nil t))
          (setq agdaprover--last-output-buffer report)
          (agdaprover--entry-test-append process "Independent entry tests: %s\n\nInspecting declarations…\n"
                                        (buffer-name source-buffer))
          (display-buffer report))
        (add-hook 'kill-buffer-hook #'agdaprover--cancel-entry-tests-on-kill nil t))
      (set-process-sentinel process #'agdaprover--sentinel)
      (process-send-string process (concat (json-serialize request) "\n"))
      (process-send-eof process)
      (when (memq (process-status process) '(exit signal))
        (agdaprover--sentinel process "finished before initialization\n"))
      (cond
       ((eq operation 'test-entries)
        (message "AgdaProver: independently testing entries with %s ranking…" ranker))
       ((eq operation 'prove-prefix)
        (message "AgdaProver: jointly searching %s with %s ranking (%s effort)..."
                 (agdaprover--prefix-progress-target goal-position)
                 ranker agdaprover-search-profile))
       (t
        (message "AgdaProver: %s goal %s with %s ranking..."
                 (if (eq operation 'step)
                     "choosing a step for"
                   "searching")
                 goal-id
                 ranker))))))

(defun agdaprover--entry-test-append (process format-string &rest arguments)
  "Append a formatted entry-test update for PROCESS."
  (when-let* ((report (process-get process 'agdaprover-entry-report)))
    (when (buffer-live-p report)
      (with-current-buffer report
        (when (eq agdaprover--entry-report-process process)
          (let ((inhibit-read-only t))
            (save-excursion
              (goto-char (point-max))
              (insert (apply #'format format-string arguments)))))))))

(defun agdaprover--entry-test-event (process envelope)
  "Render one validated streaming ENVELOPE for PROCESS, without applying edits."
  (when (and (equal (alist-get 'schema_version envelope) "agdaprover.editor.response.v1")
             (null (alist-get 'request_id envelope))
             (equal (alist-get 'status (alist-get 'result envelope)) "invalid-task"))
    (error "Cannot start entry testing: %s"
           (alist-get 'diagnostic (alist-get 'result envelope))))
  (unless (and (equal (alist-get 'request_id envelope)
                     (process-get process 'agdaprover-request-id))
               (equal (alist-get 'operation envelope) "test-entries")
               (equal (alist-get 'source_sha256 envelope)
                      (process-get process 'agdaprover-source-sha256)))
    (error "Entry-test response identity mismatch"))
  (pcase (alist-get 'schema_version envelope)
    ("agdaprover.editor.event.v1"
     (let ((payload (alist-get 'payload envelope)))
       (pcase (alist-get 'event envelope)
         ("started"
          (process-put process 'agdaprover-entry-total (alist-get 'total payload))
          (agdaprover--entry-test-append process "Testing %s entries, one at a time, in their original preceding context.\n"
                                        (alist-get 'total payload)))
         ("entry-started"
          (agdaprover--entry-test-append
           process "\n%s/%s. %s (line %s) — testing…\n"
           (alist-get 'index payload) (process-get process 'agdaprover-entry-total)
           (alist-get 'name payload) (alist-get 'line payload)))
         ("entry-result"
          (if (equal (alist-get 'status payload) "verified")
              (let ((validation (alist-get 'validation payload))
                    (solution (alist-get 'solution payload)))
                (unless (and (eq (alist-get 'fresh_process validation) t)
                             (eq (alist-get 'checked validation) t)
                             (stringp solution))
                  (error "Entry solution lacks fresh validation"))
                (agdaprover--entry-test-append
                 process "  ✓ Solved (%.2f s)\n%s\n"
                 (/ (alist-get 'elapsed_ms payload) 1000.0) solution))
            (agdaprover--entry-test-append
             process "  ✗ Unable to solve (%s): %s\n"
             (alist-get 'status payload) (or (alist-get 'diagnostic payload) ""))))
         (_ (error "Unknown entry-test event")))))
    ("agdaprover.editor.response.v1"
     (let ((result (alist-get 'result envelope)))
       (when (equal (alist-get 'status result) "completed")
         (unless (and (equal (alist-get 'schema_version result) "agdaprover.entry-tests.v1")
                      (eq (alist-get 'exit_code envelope) 0)
                      (natnump (alist-get 'total result))
                      (equal (alist-get 'solved result) (alist-get 'total result)))
           (error "Malformed entry-test completion")))
       (process-put process 'agdaprover-entry-final t)
       (agdaprover--entry-test-append
        process "\n%s: %s/%s entries solved.%s\n"
        (if (equal (alist-get 'status result) "completed") "Finished" "Stopped")
        (or (alist-get 'solved result) 0) (or (alist-get 'total result) 0)
        (if-let* ((diagnostic (alist-get 'diagnostic result)))
            (concat " " diagnostic) ""))))
    (_ (error "Unsupported entry-test response schema"))))

(defun agdaprover--entry-test-filter (process text)
  "Decode incremental JSON lines from PROCESS and display solutions as they arrive."
  (unless (or (process-get process 'agdaprover-cancelled)
              (process-get process 'agdaprover-entry-error))
    (condition-case error-data
        (let* ((source (process-get process 'agdaprover-source-buffer))
               (pending (concat (or (process-get process 'agdaprover-entry-pending) "") text))
               end)
          (unless (and (buffer-live-p source)
                       (with-current-buffer source
                         (and (eq agdaprover--process process)
                              (= (buffer-chars-modified-tick)
                                 (process-get process 'agdaprover-source-tick)))))
            (error "Source buffer changed or this run was superseded"))
          (while (setq end (string-match "\n" pending))
            (let ((line (substring pending 0 end)))
              (unless (string-empty-p line)
                (when (or (process-get process 'agdaprover-entry-final)
                          (> (string-bytes line) (* 16 1024 1024)))
                  (error "Invalid trailing or oversized entry-test response"))
                (agdaprover--entry-test-event
                 process (json-parse-string line :object-type 'alist :array-type 'list
                                            :null-object nil :false-object nil))))
            (setq pending (substring pending (1+ end))))
          (when (> (string-bytes pending) (* 16 1024 1024))
            (error "Entry-test response exceeds the protocol buffer allowance"))
          (process-put process 'agdaprover-entry-pending pending))
      (error
       (process-put process 'agdaprover-entry-error (error-message-string error-data))
       (agdaprover--stop-process process)))))

(defun agdaprover--cancel-entry-tests-on-kill ()
  "Reap an entry-test worker when its source buffer is killed."
  (when (and (process-live-p agdaprover--process)
             (eq (process-get agdaprover--process 'agdaprover-operation) 'test-entries))
    (agdaprover--entry-test-append agdaprover--process "\nSource buffer closed; entry testing cancelled.\n")
    (agdaprover--stop-process agdaprover--process)))

;;;###autoload
(defun agdaprover-test-entries ()
  "Independently test file entries using virtual holes, stopping at the first failure.
Never edit or save the source buffer or apply returned solutions.  Each entry
starts from the saved original file, with only that definition replaced.
Results appear incrementally in a separate buffer.  Cancel with C-c C-x C-k."
  (interactive)
  (agdaprover--start-operation 'test-entries agdaprover-ranker))

(defun agdaprover--start-proof (ranker)
  "Start an asynchronous proof search for the goal at point using RANKER."
  (agdaprover--start-operation 'prove ranker))

;;;###autoload
(defun agdaprover-prove-goal ()
  "Prove through the goal at point, or all goals when outside a goal."
  (interactive)
  (pcase-let ((`(,first-id ,cutoff-position ,_count)
               (agdaprover--joint-prefix-selection)))
    (agdaprover--start-operation
     'prove-prefix agdaprover-ranker first-id cutoff-position)))

;;;###autoload
(defun agdaprover-prove-deep ()
  "Jointly prove through point, or all goals, with the deep effort preset.
Explicit `agdaprover-max-candidates' and other resource limits remain active."
  (interactive)
  (let ((agdaprover-search-profile 'deep))
    (agdaprover-prove-goal)))

;;;###autoload
(defun agdaprover-prove-goal-symbolic ()
  "Prove the agda-mode goal at point using deterministic symbolic ranking."
  (interactive)
  (agdaprover--start-proof 'symbolic))

;;;###autoload
(defun agdaprover-prove-goal-nnue ()
  "Prove the agda-mode goal at point using the configured NNUE model."
  (interactive)
  (agdaprover--start-proof 'nnue))

;;;###autoload
(defun agdaprover-reserved-n ()
  "Do nothing; reserve `C-c C-x C-n' for a future AgdaProver operation."
  (interactive)
  (message "AgdaProver: C-c C-x C-n is reserved for a future command"))

;;;###autoload
(defun agdaprover-step-goal ()
  "Choose and apply one Agda refinement using the configured step ranker."
  (interactive)
  (agdaprover--start-operation
   'step (or agdaprover-step-ranker agdaprover-ranker)))

;;;###autoload
(defun agdaprover-step-goal-nnue ()
  "Choose and apply one Agda refinement using the one-step NNUE model."
  (interactive)
  (agdaprover--start-operation 'step 'nnue))

;;;###autoload
(defun agdaprover-cancel ()
  "Cancel the active AgdaProver search in the current buffer."
  (interactive)
  (unless (process-live-p agdaprover--process)
    (user-error "No AgdaProver search is running in this buffer"))
  (agdaprover--stop-process agdaprover--process))

(defun agdaprover--stop-process (process)
  "Interrupt PROCESS cooperatively, with a bounded hard-stop fallback."
  (when (process-live-p process)
    (process-put process 'agdaprover-cancelled t)
    ;; SIGINT lets Python unwind its active bridge/session context managers,
    ;; which cancel and reap the separate Agda process group.  Retain a bounded
    ;; hard-stop only for a CLI that fails to honor the cooperative signal.
    (interrupt-process process)
    (run-at-time
     2 nil
     (lambda (candidate)
       (when (process-live-p candidate)
         (delete-process candidate)))
     process)))

;;;###autoload
(defun agdaprover-apply-last-proof ()
  "Apply the last fresh-validated proof if its source snapshot is current."
  (interactive)
  (unless agdaprover--last-result
    (user-error "No AgdaProver result is available in this buffer"))
  (unless (equal (alist-get 'status agdaprover--last-result) "verified")
    (user-error "The last AgdaProver result was not verified"))
  (unless (agdaprover--buffer-snapshot-current-p
           (current-buffer)
           agdaprover--last-source-tick
           agdaprover--last-goal-id
           agdaprover--last-goal-marker)
    (user-error "The buffer changed after proof search; refusing to apply stale proof"))
  (agdaprover--apply-result agdaprover--last-result agdaprover--last-goal-id))

;;;###autoload
(defun agdaprover-show-last-result ()
  "Display the complete JSON result from the last proof search."
  (interactive)
  (unless (buffer-live-p agdaprover--last-output-buffer)
    (user-error "No AgdaProver result buffer is available"))
  (display-buffer agdaprover--last-output-buffer))

;;;###autoload
(defun agdaprover-reload ()
  "Reload the installed AgdaProver editor source without restarting Emacs.
Use the checkout from which this mode was loaded, not the configurable
backend path.  Read the .el source even when compiled copies exist.
Preserve settings, enabled buffers, and their last results.  Finish or
cancel AgdaProver runs in all buffers first, including pending results.
This command does not download updates or reload Agda source files."
  (interactive)
  (when-let* ((busy-buffer
              (cl-find-if
               (lambda (buffer)
                 ;; A finished child can still have a pending sentinel.
                 (buffer-local-value 'agdaprover--process buffer))
               (buffer-list))))
    (user-error "Finish or cancel the AgdaProver run in %s before reloading"
                (buffer-name busy-buffer)))
  (let ((source (expand-file-name "editor/agdaprover.el"
                                 agdaprover--default-project-root)))
    (unless (and (file-regular-p source) (file-readable-p source))
      (user-error "AgdaProver editor source is missing or unreadable: %s" source))
    ;; Do not unload the feature or toggle modes: either would discard state
    ;; or rerun user hooks.  NOSUFFIX avoids stale byte/native-compiled copies.
    (save-excursion
      (load source nil t t))
    (message "AgdaProver: reloaded editor mode from %s" source)))

(defvar agdaprover-mode-map (make-sparse-keymap)
  "Keymap for `agdaprover-mode'.")

(defvar agdaprover--installed-keybindings nil
  "Default key bindings installed by the most recently loaded mode source.")

(defun agdaprover--install-keybindings (bindings)
  "Refresh default BINDINGS in place, preserving user-customized keys.
BINDINGS is an alist from key descriptions to commands.  Updating the
existing map also updates buffers in which the mode is already enabled."
  (dolist (old agdaprover--installed-keybindings)
    (when (and (not (assoc (car old) bindings))
               (eq (lookup-key agdaprover-mode-map (kbd (car old))) (cdr old)))
      (define-key agdaprover-mode-map (kbd (car old)) nil)))
  (dolist (binding bindings)
    (let* ((key (kbd (car binding)))
           (old (assoc (car binding) agdaprover--installed-keybindings))
           (current (lookup-key agdaprover-mode-map key)))
      (when (numberp current)
        (setq current (lookup-key agdaprover-mode-map (cl-subseq key 0 current))))
      (when (if old (eq current (cdr old)) (null current))
        (define-key agdaprover-mode-map key (cdr binding)))))
  (setq agdaprover--installed-keybindings bindings))

(agdaprover--install-keybindings
 '(("C-c C-x C-p" . agdaprover-prove-goal)
   ("C-c C-x C-d" . agdaprover-prove-deep)
   ("C-c C-x C-s" . agdaprover-step-goal)
   ("C-c C-x C-n" . agdaprover-reserved-n)
   ("C-c C-x C-v" . agdaprover-apply-last-proof)
   ("C-c C-x C-k" . agdaprover-cancel)
   ("C-c C-x C-t" . agdaprover-test-entries)
   ("C-c C-x C-q" . agdaprover-reload)))

(easy-menu-define agdaprover-mode-menu agdaprover-mode-map
  "Menu for AgdaProver commands."
  '("AgdaProver"
    ["Prove through current goal, or all goals" agdaprover-prove-goal t]
    ["Deep search through current goal, or all goals" agdaprover-prove-deep t]
    ["Test file entries independently" agdaprover-test-entries t]
    ["Take one refinement step" agdaprover-step-goal t]
    ["Take one step with NNUE" agdaprover-step-goal-nnue t]
    ["Prove goal symbolically" agdaprover-prove-goal-symbolic t]
    ["Apply last verified proof" agdaprover-apply-last-proof
     agdaprover--last-result]
    ["Show last result" agdaprover-show-last-result
     agdaprover--last-output-buffer]
    ["Cancel search" agdaprover-cancel
     (process-live-p agdaprover--process)]
    "---"
    ["Reload AgdaProver editor mode" agdaprover-reload t]))

;;;###autoload
(define-minor-mode agdaprover-mode
  "Use the local AgdaProver prototype from an Agda or literate Agda buffer."
  :lighter " AgdaP"
  :keymap agdaprover-mode-map
  :group 'agdaprover
  (when (and agdaprover-mode (not (derived-mode-p 'agda2-mode)))
    (setq agdaprover-mode nil)
    (user-error "`agdaprover-mode' only supports agda-mode buffers")))

(provide 'agdaprover)

;;; agdaprover.el ends here
