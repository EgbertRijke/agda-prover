;;; agdaprover-test.el --- Tests for agdaprover.el -*- lexical-binding: t; -*-

(require 'ert)
(defvar agdaprover-test--real-agda-mode-p (require 'agda2-mode nil t))
(unless agdaprover-test--real-agda-mode-p
  ;; Keep pure editor-contract tests runnable on CI workers without Agda.  The
  ;; real integration tests below still require the pinned local toolchain.
  (define-derived-mode agda2-mode prog-mode "Agda")
  (defvar agda2-in-progress nil)
  (provide 'agda2-mode))
(require 'agdaprover)

(defconst agdaprover-test--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory load-file-name))))

(defun agdaprover-test--supported-agda-p ()
  "Return non-nil when the P0-pinned Agda 2.8.0 is executable."
  (when-let* ((executable (and agdaprover-test--real-agda-mode-p
                             (executable-find "agda"))))
    (with-temp-buffer
      (and (zerop (call-process executable nil t nil "--numeric-version"))
           (equal (string-trim (buffer-string)) "2.8.0")))))

(defun agdaprover-test--wait-until (predicate timeout)
  "Wait up to TIMEOUT seconds for PREDICATE while processing events."
  ;; An exited process can still have a pending sentinel.  Integration tests
  ;; wait for the sentinel to clear `agdaprover--process', not just OS exit.
  (let ((deadline (+ (float-time) timeout)))
    (while (and (not (funcall predicate)) (< (float-time) deadline))
      (accept-process-output nil 0.05))
    (funcall predicate)))

(ert-deftest agdaprover-test-command-symbolic ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-max-candidates 12)
        (agdaprover-max-term-size 7)
        (agdaprover-timeout 9))
    (should
     (equal
      (agdaprover--command "/tmp/Tiny.agda" 4 'symbolic)
      '("python3" "-m" "agdaprover" "prove" "/tmp/Tiny.agda"
        "--goal-position" "4" "--ranker" "symbolic"
        "--max-candidates" "12" "--max-term-size" "7"
        "--timeout" "9")))))

(ert-deftest agdaprover-test-command-omits-unconfigured-wall-time-limit ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-timeout nil))
    (should-not
     (member "--timeout"
             (agdaprover--command "/tmp/Tiny.agda" 4 'symbolic)))))

(ert-deftest agdaprover-test-deep-profile-shares-editor-and-cli-contract ()
  (let* ((agdaprover-search-profile 'deep)
         (agdaprover-max-candidates nil)
         (source (expand-file-name "examples/EckmannHilton.agda" agdaprover-test--root))
         (command (agdaprover--prefix-command source 1 'symbolic))
         (request (agdaprover--editor-request "test:deep" 'prove-prefix source 1 'symbolic nil)))
    (should (equal (cadr (member "--search-profile" command)) "deep"))
    (should-not (member "--max-candidates" command))
    (should (equal (alist-get 'search_profile request) "deep"))
    (should-not (assq 'max_candidates request))
    (let ((agdaprover-max-candidates 17))
      (should (= (alist-get 'max_candidates
                           (agdaprover--editor-request "test:deep" 'prove-prefix source 1 'symbolic nil))
                 17)))))

(ert-deftest agdaprover-test-deep-command-keeps-normal-selection-and-restores-profile ()
  (let ((agdaprover-search-profile 'standard)
        observed)
    (cl-letf (((symbol-function 'agdaprover-prove-goal)
               (lambda () (setq observed agdaprover-search-profile))))
      (agdaprover-prove-deep))
    (should (eq observed 'deep))
    (should (eq agdaprover-search-profile 'standard))
    (should (eq (lookup-key agdaprover-mode-map (kbd "C-c C-x C-d"))
                #'agdaprover-prove-deep))))

(ert-deftest agdaprover-test-literate-markdown-uses-agda-mode ()
  (should (eq (assoc-default "Example.lagda.md" auto-mode-alist
                             #'string-match-p)
              'agda2-mode)))

(ert-deftest agdaprover-test-command-step-nnue ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-step-model-file "/tmp/step.apnnue")
        (agdaprover-max-candidates 12)
        (agdaprover-max-term-size 7)
        (agdaprover-timeout 9))
    (cl-letf (((symbol-function 'file-readable-p) (lambda (_path) t)))
      (should
       (equal
        (agdaprover--step-command "/tmp/Tiny.agda" 17 'nnue)
        '("python3" "-m" "agdaprover" "step" "/tmp/Tiny.agda"
          "--goal-position" "17" "--ranker" "nnue"
          "--max-candidates" "12" "--max-term-size" "7"
          "--timeout" "9" "--model" "/tmp/step.apnnue"))))))

(ert-deftest agdaprover-test-step-never-reuses-proof-model ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-model-file "/tmp/policy.apnnue")
        (agdaprover-step-model-file nil))
    (should-error
     (agdaprover--step-command "/tmp/Tiny.agda" 17 'nnue)
     :type 'user-error)))

(ert-deftest agdaprover-test-command-joint-prefix ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-max-candidates 12)
        (agdaprover-max-term-size 7)
        (agdaprover-timeout 9))
    (should
     (equal
      (agdaprover--prefix-command "/tmp/Tiny.agda" 41 'symbolic)
      '("python3" "-m" "agdaprover" "prove-prefix" "/tmp/Tiny.agda"
        "--goal-position" "41" "--ranker" "symbolic"
        "--max-candidates" "12" "--max-term-size" "7"
        "--timeout" "9")))))

(ert-deftest agdaprover-test-command-with-depth-budget ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-max-candidates 12)
        (agdaprover-max-term-size 7)
        (agdaprover-max-depth 5)
        (agdaprover-timeout 9))
    (should
     (equal
      (agdaprover--command "/tmp/Tiny.agda" 4 'symbolic)
      '("python3" "-m" "agdaprover" "prove" "/tmp/Tiny.agda"
        "--goal-position" "4" "--ranker" "symbolic"
        "--max-candidates" "12" "--max-term-size" "7"
        "--timeout" "9" "--max-depth" "5")))))

(ert-deftest agdaprover-test-unified-proof-command-uses-both-nnue-roles ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-python-command "python3")
        (agdaprover-model-file "/tmp/policy.apnnue")
        (agdaprover-step-model-file "/tmp/step.apnnue")
        (agdaprover-action-model-file "/tmp/actions.apnnue")
        (agdaprover-max-candidates 12)
        (agdaprover-max-term-size 7)
        (agdaprover-timeout 9))
    (cl-letf (((symbol-function 'file-readable-p) (lambda (_path) t)))
      (should
       (equal
        (agdaprover--command "/tmp/Tiny.agda" 4 'nnue)
        '("python3" "-m" "agdaprover" "prove" "/tmp/Tiny.agda"
          "--goal-position" "4" "--ranker" "nnue"
          "--max-candidates" "12" "--max-term-size" "7"
          "--timeout" "9" "--model" "/tmp/policy.apnnue"
          "--action-model" "/tmp/actions.apnnue"))))))

(ert-deftest agdaprover-test-proof-never-reuses-one-step-model-as-action-model ()
  (let ((agdaprover-step-model-file "/tmp/step.apnnue")
        (agdaprover-action-model-file nil))
    (should-not (agdaprover--action-model-for-operation 'prove))
    (should-not (agdaprover--action-model-for-operation 'prove-prefix))
    (should-not (agdaprover--action-model-for-operation 'step)))
  (let ((agdaprover-step-model-file "/tmp/step.apnnue")
        (agdaprover-action-model-file "/tmp/or-decisions.apnnue"))
    (should (equal (agdaprover--action-model-for-operation 'prove-prefix)
                   "/tmp/or-decisions.apnnue"))
    (should-not (agdaprover--action-model-for-operation 'step))))

(ert-deftest agdaprover-test-guided-proof-applies-validated-source-edit ()
  (with-temp-buffer
    (insert "f b = {! !}")
    (let ((result
           '((schema_version . "agdaprover.p0.v1")
             (status . "verified")
             (proof_term . "f false = refl\nf true = refl")
             (validation . ((checked . t)))
             (trust_report . ((agda_version . "test")))
             (patch
              (schema_version . "agdaprover.reconstruction.p0.v1")
              (style . "guided-clauses")
              (source_range . (1 12))
              (original . "f b = {! !}")
              (replacement . "f false = refl\nf true = refl"))))
          (loaded nil))
      (cl-letf (((symbol-function 'agda2-goal-overlay) (lambda (_goal) t))
                ((symbol-function 'agda2-load) (lambda () (setq loaded t))))
        (agdaprover--apply-result result 0))
      (should loaded)
      (should (equal (buffer-string) "f false = refl\nf true = refl")))))

(ert-deftest agdaprover-test-joint-proof-applies-one-atomic-source-edit ()
  (with-temp-buffer
    (insert "choose = {!!}\nlaw = {!!}")
    (let ((result
           '((schema_version . "agdaprover.p0.v1")
             (status . "verified")
             (proof_term . "choose x y = y\nlaw = refl")
             (validation . ((checked . t)))
             (trust_report . ((agda_version . "test")))
             (joint_goals . (((goal_id . 0)) ((goal_id . 1))))
             (patch
              (schema_version . "agdaprover.reconstruction.p0.v1")
              (style . "joint-clauses")
              (source_range . (1 25))
              (target_goal_count . 2)
              (cutoff_position . 21)
              (steps
               . (((schema_version . "agdaprover.reconstruction.p0.v1")
                   (style . "guided-clauses")
                   (source_range . (1 14))
                   (original . "choose = {!!}")
                   (replacement . "choose x y = y")
                   (binders . ())
                   (body . "choose x y = y"))
                  ((schema_version . "agdaprover.reconstruction.p0.v1")
                   (style . "guided-clauses")
                   (source_range . (16 26))
                   (original . "law = {!!}")
                   (replacement . "law = refl")
                   (binders . ())
                   (body . "law = refl"))))
              (original . "choose = {!!}\nlaw = {!!}")
              (replacement . "choose x y = y\nlaw = refl"))))
          (loaded nil))
      (cl-letf (((symbol-function 'agda2-goal-overlay) (lambda (_goal) t))
                ((symbol-function 'agda2-load) (lambda () (setq loaded t))))
        (agdaprover--apply-result result 0))
      (should loaded)
      (should (equal (buffer-string) "choose x y = y\nlaw = refl")))))

(ert-deftest agdaprover-test-joint-replay-accepts-formatted-block-clause ()
  (let ((step
         '((schema_version . "agdaprover.reconstruction.p0.v1")
           (style . "clause")
           (source_range . (1 12))
           (original . "long = {!!}")
           (replacement . "long x =\n  f\n    x")
           (binders . ("x"))
           (body . "f\n    x")
           (layout . "next-line"))))
    (should (agdaprover--joint-step-shape-p step))
    (setf (alist-get 'replacement step) "long x = f\n    x")
    (should-not (agdaprover--joint-step-shape-p step))))

(ert-deftest agdaprover-test-formatter-metadata-is-versioned ()
  (let ((metadata
         `((schema_version . "agdaprover.proof-formatter.v1")
           (profile . "agda-unimath-v1")
           (scope . "generated-proof-term")
           (status . "formatted")
           (changed . t)
           (line_width . 80)
           (input_sha256 . ,(make-string 64 ?a))
           (output_sha256 . ,(make-string 64 ?b)))))
    (should (agdaprover--formatter-metadata-p metadata))
    (setf (alist-get 'schema_version metadata) "future")
    (should-not (agdaprover--formatter-metadata-p metadata))))

(ert-deftest agdaprover-test-nnue-requires-model ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (agdaprover-model-file nil))
    (should-error
     (agdaprover--command "/tmp/Tiny.agda" 0 'nnue)
     :type 'user-error)))

(ert-deftest agdaprover-test-auto-ranker-prefers-nnue-with-model ()
  (cl-letf (((symbol-function 'file-readable-p) (lambda (_path) t)))
    (should (eq (agdaprover--resolve-ranker 'auto "/tmp/policy.apnnue")
                'nnue)))
  (should (eq (agdaprover--resolve-ranker 'auto nil) 'symbolic)))

(ert-deftest agdaprover-test-n-key-is-reserved-no-op ()
  (should (eq (lookup-key agdaprover-mode-map (kbd "C-c C-x C-n"))
              #'agdaprover-reserved-n)))

(ert-deftest agdaprover-test-cancel-interrupts-before-bounded-hard-stop ()
  (let* ((process (make-pipe-process :name "agdaprover-cancel-test"
                                     :noquery t))
         (agdaprover--process process)
         (interrupted nil)
         (scheduled nil))
    (unwind-protect
        (cl-letf (((symbol-function 'interrupt-process)
                   (lambda (candidate)
                     (should (eq candidate process))
                     (setq interrupted t)))
                  ((symbol-function 'run-at-time)
                   (lambda (delay repeat function &rest arguments)
                     (should (= delay 2))
                     (should-not repeat)
                     (should (functionp function))
                     (should (equal arguments (list process)))
                     (setq scheduled t))))
          (agdaprover-cancel)
          (should interrupted)
          (should scheduled)
          (should (process-get process 'agdaprover-cancelled)))
      (when (process-live-p process)
        (delete-process process)))))

(ert-deftest agdaprover-test-superseded-process-cannot-apply-stale-result ()
  (with-temp-buffer
    (let* ((source-buffer (current-buffer))
           (output-buffer (generate-new-buffer " *agdaprover-old-output*"))
           (old-process
            (make-process :name "agdaprover-old-process"
                          :buffer output-buffer
                          :command '("true")
                          :sentinel #'ignore
                          :noquery t))
           (new-process
            (make-pipe-process :name "agdaprover-new-process" :noquery t))
           (parsed nil)
           (agdaprover--process new-process)
           (agdaprover--last-result '((status . "newer"))))
      (unwind-protect
          (progn
            (while (process-live-p old-process)
              (accept-process-output old-process 0.05))
            (process-put old-process 'agdaprover-source-buffer source-buffer)
            (process-put old-process 'agdaprover-source-tick
                         (buffer-chars-modified-tick))
            (process-put old-process 'agdaprover-goal-id 0)
            (process-put old-process 'agdaprover-goal-marker
                         (copy-marker (point-min)))
            (cl-letf (((symbol-function 'agdaprover--parse-json-buffer)
                       (lambda (_buffer) (setq parsed t))))
              (agdaprover--sentinel old-process "finished\n"))
            (should-not parsed)
            (should (eq agdaprover--process new-process))
            (should (equal (alist-get 'status agdaprover--last-result)
                           "newer")))
        (when (process-live-p new-process)
          (delete-process new-process))
        (when (buffer-live-p output-buffer)
          (kill-buffer output-buffer))))))

(ert-deftest agdaprover-test-joint-prefix-uses-goal-at-cursor-as-cutoff ()
  (with-temp-buffer
    (insert "first {! !} middle {! !} last")
    (let ((first (make-overlay 7 12))
          (second (make-overlay 20 25))
          (visited nil))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t))
                ((symbol-function 'agda2-goto-goal)
                 (lambda (goal-id) (setq visited goal-id))))
        (goto-char 22)
        (should (equal (agdaprover--joint-prefix-selection) '(9 20 2)))
        (should (= visited 9))))))

(ert-deftest agdaprover-test-joint-prefix-selects-all-goals-between-holes ()
  (with-temp-buffer
    (insert "first {! !} middle {! !} last")
    (let ((first (make-overlay 7 12))
          (second (make-overlay 20 25)))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t))
                ((symbol-function 'agda2-goto-goal) #'ignore))
        (goto-char 15)
        (should (equal (agdaprover--joint-prefix-selection) '(9 15 2)))))))

(ert-deftest agdaprover-test-joint-prefix-selects-all-goals-after-last-goal ()
  (with-temp-buffer
    (insert "first {! !} last")
    (let ((first (make-overlay 7 12)))
      (overlay-put first 'agda2-gn 9)
      (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t))
                ((symbol-function 'agda2-goto-goal) #'ignore))
        (goto-char (point-max))
        (should (equal (agdaprover--joint-prefix-selection)
                       (list 9 (point-max) 1)))))))

(ert-deftest agdaprover-test-joint-prefix-selects-all-goals-before-first-goal ()
  (with-temp-buffer
    (insert "before {! !} middle {! !}")
    (let ((first (make-overlay 8 13))
          (second (make-overlay 21 26)))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t))
                ((symbol-function 'agda2-goto-goal) #'ignore))
        (goto-char 1)
        (should (equal (agdaprover--joint-prefix-selection) '(9 1 2)))))))

(ert-deftest agdaprover-test-joint-prefix-stops-at-containing-goal ()
  (with-temp-buffer
    (insert "first {! !} middle {! !} last")
    (let ((first (make-overlay 7 12))
          (second (make-overlay 20 25)))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t))
                ((symbol-function 'agda2-goto-goal) #'ignore))
        (goto-char 9)
        (should (equal (agdaprover--joint-prefix-selection) '(9 7 1)))))))

(ert-deftest agdaprover-test-prefix-progress-names-the-cutoff-not-the-anchor ()
  (with-temp-buffer
    (insert "first {! !} middle {! !} last")
    (let ((first (make-overlay 7 12))
          (second (make-overlay 20 25)))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (should
       (equal (agdaprover--prefix-progress-target 20)
              "through goal 2 (2 selected goals)"))
      (should-not
       (string-match-p "goal 9"
                       (agdaprover--prefix-progress-target 20))))))

(ert-deftest agdaprover-test-prefix-progress-reports-whole-file-selection ()
  (with-temp-buffer
    (insert "first {! !} middle {! !} last")
    (let ((first (make-overlay 7 12))
          (second (make-overlay 20 25)))
      (overlay-put first 'agda2-gn 9)
      (overlay-put second 'agda2-gn 2)
      (should
       (equal (agdaprover--prefix-progress-target 15)
              "all 2 open goals")))))

(ert-deftest agdaprover-test-joint-prefix-requires-a-loaded-goal ()
  (with-temp-buffer
    (cl-letf (((symbol-function 'derived-mode-p) (lambda (_mode) t)))
      (should-error (agdaprover--joint-prefix-selection) :type 'user-error))))

(ert-deftest agdaprover-test-json-result-parsing ()
  (with-temp-buffer
    (insert "{\"schema_version\":\"agdaprover.p0.v1\","
            "\"status\":\"verified\",\"proof_term\":\"refl\"}")
    (let ((result (agdaprover--parse-json-buffer (current-buffer))))
      (should (equal (alist-get 'status result) "verified"))
      (should (equal (alist-get 'proof_term result) "refl")))))

(ert-deftest agdaprover-test-first-diagnostic-supports-editor-errors ()
  (should
   (equal
    (agdaprover--first-diagnostic
     '((status . "invalid-task")
       (diagnostic . "NNUE role mismatch")))
    "NNUE role mismatch")))

(ert-deftest agdaprover-test-malformed-verified-result-is-never-applied ()
  (with-temp-buffer
    (let* ((source-buffer (current-buffer))
           (output-buffer (generate-new-buffer " *agdaprover-malformed*"))
           (marker (copy-marker (point-min)))
           (shown nil)
           (result '((schema_version . "agdaprover.p0.v1")
                     (status . "verified")
                     (proof_term . "refl"))))
      (unwind-protect
          (cl-letf (((symbol-function 'display-buffer)
                     (lambda (&rest _arguments) (setq shown t))))
            (agdaprover--offer-result
             source-buffer result (buffer-chars-modified-tick) 0 marker
             output-buffer)
            (should shown))
        (when (buffer-live-p output-buffer)
          (kill-buffer output-buffer))))))

(ert-deftest agdaprover-test-impossible-result-is-concise ()
  (with-temp-buffer
    (let* ((source-buffer (current-buffer))
           (output-buffer (generate-new-buffer " *agdaprover-impossible*"))
           (marker (copy-marker (point-min)))
           (shown nil)
           (notice nil)
           (result
            '((status . "impossible")
              (diagnostics
               . (((kind . "impossibility")
                   (message . "This goal is impossible: Agda checked a refutation of its complete polymorphic type.")))))))
      (unwind-protect
          (cl-letf (((symbol-function 'display-buffer)
                     (lambda (&rest _arguments) (setq shown t)))
                    ((symbol-function 'message)
                     (lambda (format-string &rest arguments)
                       (setq notice (apply #'format format-string arguments)))))
            (agdaprover--offer-result
             source-buffer result (buffer-chars-modified-tick) 0 marker
             output-buffer)
            (should-not shown)
            (should
             (equal notice
                    "AgdaProver: This goal is impossible: Agda checked a refutation of its complete polymorphic type.")))
        (when (buffer-live-p output-buffer)
          (kill-buffer output-buffer))))))

(ert-deftest agdaprover-test-stale-buffer-protection ()
  (with-temp-buffer
    (insert "{! !}")
    (let* ((overlay (make-overlay (point-min) (point-max)))
           (marker (copy-marker (+ (point-min) 2)))
           (tick (buffer-chars-modified-tick)))
      (overlay-put overlay 'agda2-gn 3)
      (cl-letf (((symbol-function 'agda2-goal-overlay)
                 (lambda (goal-id) (and (= goal-id 3) overlay))))
        (should
         (agdaprover--buffer-snapshot-current-p
          (current-buffer) tick 3 marker))
        (goto-char (point-max))
        (insert " changed")
        (should-not
         (agdaprover--buffer-snapshot-current-p
          (current-buffer) tick 3 marker))))))

(ert-deftest agdaprover-test-process-environment-preserves-existing-path ()
  (let ((agdaprover-project-root agdaprover-test--root)
        (process-environment (copy-sequence process-environment)))
    (setenv "PYTHONPATH" "/existing")
    (let ((environment (agdaprover--process-environment)))
      (let ((process-environment environment))
        (should
         (string-match-p
          (regexp-quote (expand-file-name "src" agdaprover-test--root))
          (getenv "PYTHONPATH")))
        (should (string-match-p "/existing" (getenv "PYTHONPATH")))))))

(ert-deftest agdaprover-test-real-goal-search ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-emacs-" t))
         (fixture (expand-file-name "tests/fixtures/Identity.agda"
                                    agdaprover-test--root))
         (source (expand-file-name "Identity.agda" temporary-directory))
         (_copied (copy-file fixture source t))
         (buffer (find-file-noselect source))
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-apply-policy 'always))
    (unwind-protect
        (with-current-buffer buffer
          (agda2-mode)
          (agda2-load)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (agda2-goal-overlay 0)))
            10))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
          (agdaprover-mode 1)
          (agdaprover-prove-goal-symbolic)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            agdaprover--last-result))
            20))
          (should (equal (alist-get 'status agdaprover--last-result)
                         "verified"))
          (should (equal (alist-get 'proof_term agdaprover--last-result)
                         "λ x0 → x0"))
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (not (agda2-goal-overlay 0))))
            10))
          (goto-char (point-min))
          (should (search-forward "identity x0 = x0" nil t)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-real-literate-goal-search-preserves-prose ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-literate-emacs-" t))
         (fixture-directory (expand-file-name "tests/fixtures"
                                              agdaprover-test--root))
         (source (expand-file-name "LiterateIdentity.lagda.md"
                                   temporary-directory))
         (_source-copied
          (copy-file (expand-file-name "LiterateIdentity.lagda.md"
                                      fixture-directory)
                     source t))
         (_support-copied
          (copy-file (expand-file-name "Support.lagda.md" fixture-directory)
                     (expand-file-name "Support.lagda.md" temporary-directory) t))
         (buffer (find-file-noselect source))
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-apply-policy 'always))
    (unwind-protect
        (with-current-buffer buffer
          (should (derived-mode-p 'agda2-mode))
          (agda2-load)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (agda2-goal-overlay 0)))
            10))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
          (agdaprover-mode 1)
          (agdaprover-prove-goal-symbolic)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            agdaprover--last-result
                            (not agda2-in-progress)))
            20))
          (should (equal (alist-get 'status agdaprover--last-result)
                         "verified"))
          (goto-char (point-min))
          (should (search-forward "# A checked proof inside Markdown" nil t))
          (should (search-forward "identity-again x0 = x0" nil t))
          (should (search-forward "```" nil t))
          (should-not (agda2-goal-overlay 0)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-prompts-when-other-holes-remain ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-partial-emacs-" t))
         (source (expand-file-name "Partial.agda" temporary-directory))
         (buffer nil)
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-apply-policy 'ask)
         (prompt nil))
    (with-temp-file source
      (insert "module Partial where\n\n"
              "compose : {A B C : Set} → (A → B) → (B → C) → A → C\n"
              "compose = {!!}\n\n"
              "identity : {A : Set} → A → A\n"
              "identity = {!!}\n"))
    (setq buffer (find-file-noselect source))
    (unwind-protect
        (cl-letf (((symbol-function 'y-or-n-p)
                   (lambda (message)
                     (setq prompt message)
                     nil)))
          (with-current-buffer buffer
            (agda2-mode)
            (agda2-load)
            (should
             (agdaprover-test--wait-until
              (lambda () (and (not agda2-in-progress)
                              (agda2-goal-overlay 0)))
              10))
            (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
            (agdaprover-mode 1)
            (let ((agdaprover-ranker 'symbolic))
              (call-interactively
               (lookup-key agdaprover-mode-map (kbd "C-c C-x C-p"))))
            (should (equal (cadr (agda2-goal-at (point))) 0))
            (should
             (agdaprover-test--wait-until
              (lambda ()
                (and (null agdaprover--process)
                     agdaprover--last-result))
              20))
            (should (equal (alist-get 'status agdaprover--last-result)
                           "verified"))
            (should (string-match-p "Apply it?" prompt))
            (goto-char (point-min))
            (should (search-forward "compose = {!!}" nil t))))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-real-joint-prefix-backtracks-across-declarations ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-joint-emacs-" t))
         (fixture (expand-file-name "tests/fixtures/ChoiceConstrainedByLaw.agda"
                                    agdaprover-test--root))
         (source (expand-file-name "ChoiceConstrainedByLaw.agda"
                                   temporary-directory))
         (_copied (copy-file fixture source t))
         (buffer (find-file-noselect source))
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-ranker 'symbolic)
         (agdaprover-apply-policy 'always))
    (unwind-protect
        (with-current-buffer buffer
          (agda2-mode)
          (agda2-load)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (agda2-goal-overlay 0)
                            (agda2-goal-overlay 1)))
            10))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 1))))
          (agdaprover-mode 1)
          (agdaprover-prove-goal)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            agdaprover--last-result
                            (not agda2-in-progress)))
            20))
          (should (equal (alist-get 'status agdaprover--last-result)
                         "verified"))
          (should (= (length (alist-get 'joint_goals agdaprover--last-result))
                     2))
          (goto-char (point-min))
          (should (re-search-forward "^select [^:]* =" nil t))
          (beginning-of-line)
          (let ((clause (buffer-substring-no-properties
                         (line-beginning-position) (line-end-position))))
            (should (string-match
                     "^select \\([^ ]+\\) \\([^ ]+\\) = \\([^ ]+\\)$"
                     clause))
            (should (equal (match-string 2 clause) (match-string 3 clause))))
          ;; Generated clauses may preserve source binder names or choose
          ;; alpha-equivalent fresh names; editor acceptance is semantic.
          (should (re-search-forward
                   "select-right [^ \n]+ [^ \n]+ = refl" nil t))
          (should-not (agda2-goal-overlay 0))
          (should-not (agda2-goal-overlay 1)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-real-two-step-refinement ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-step-emacs-" t))
         (fixture (expand-file-name "tests/fixtures/Identity.agda"
                                    agdaprover-test--root))
         (source (expand-file-name "Identity.agda" temporary-directory))
         (_copied (copy-file fixture source t))
         (buffer (find-file-noselect source))
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-ranker 'symbolic))
    (unwind-protect
        (with-current-buffer buffer
          (agda2-mode)
          (agda2-load)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (agda2-goal-overlay 0)))
            10))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
          (agdaprover-mode 1)
          (agdaprover-step-goal)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            (not agda2-in-progress)
                            (agda2-goal-overlay 0)))
            20))
          (should (equal (alist-get 'status agdaprover--last-step-result)
                         "accepted-step"))
          (should (equal (alist-get 'tag
                                    (alist-get 'action agdaprover--last-step-result))
                         "introduce-lambda"))
          (goto-char (point-min))
          (should (search-forward "identity x = {! !}" nil t))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
          (agdaprover-step-goal)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            (not agda2-in-progress)
                            (not (agda2-goal-overlay 0))))
            20))
          (goto-char (point-min))
          (should (search-forward "identity x = x" nil t)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-real-multi-binder-step ()
  (skip-unless (agdaprover-test--supported-agda-p))
  (let* ((temporary-directory (make-temp-file "agdaprover-multi-step-emacs-" t))
         (source (expand-file-name "MultiStep.agda" temporary-directory))
         (buffer nil)
         (agdaprover-project-root agdaprover-test--root)
         (agdaprover-step-ranker 'symbolic))
    (with-temp-file source
      (insert "module MultiStep where\n\n"
              "compose : {A B C : Set} → (A → B) → (B → C) → A → C\n"
              "compose = {!!}\n\n"
              "identity : {A : Set} → A → A\n"
              "identity = {!!}\n"))
    (setq buffer (find-file-noselect source))
    (unwind-protect
        (with-current-buffer buffer
          (agda2-mode)
          (agda2-load)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (not agda2-in-progress)
                            (agda2-goal-overlay 0)))
            10))
          (goto-char (+ 2 (overlay-start (agda2-goal-overlay 0))))
          (agdaprover-mode 1)
          (agdaprover-step-goal)
          (should
           (agdaprover-test--wait-until
            (lambda () (and (null agdaprover--process)
                            (not agda2-in-progress)))
            20))
          (should (equal (alist-get 'status agdaprover--last-step-result)
                         "accepted-step"))
          (goto-char (point-min))
          (should (search-forward "compose x x₁ x₂ = {!!}" nil t)))
      (when (buffer-live-p buffer)
        (with-current-buffer buffer
          (when (agda2-running-p)
            (agda2-quit))
          (set-buffer-modified-p nil))
        (kill-buffer buffer))
      (delete-directory temporary-directory t))))

(ert-deftest agdaprover-test-explicit-library-configuration ()
  (let ((agdaprover-agda-executable nil)
        (agdaprover-library-file nil)
        (agdaprover-agda-options nil))
    (should-not (agdaprover--project-configuration))
    (setq agdaprover-library-file "registry with spaces")
    (let ((configuration (agdaprover--project-configuration)))
      (should (equal (alist-get 'schema_version configuration)
                     "agdaprover.project-configuration.v1"))
      (should (equal (alist-get 'options configuration)
                     ["--without-K" "--exact-split"]))
      (should (file-name-absolute-p (alist-get 'library_file configuration)))))
  (let ((agdaprover-agda-options '("--safe")))
    (should (equal (alist-get 'options (agdaprover--project-configuration))
                   ["--safe"])))
  (let ((agdaprover-agda-options [])
        (agdaprover-agda-executable "./toolchain/agda"))
    (should (equal (alist-get 'options (agdaprover--project-configuration)) []))
    (should (equal (alist-get 'executable (agdaprover--project-configuration))
                   (expand-file-name "./toolchain/agda")))))

(provide 'agdaprover-test)

;;; agdaprover-test.el ends here
