//! Small proof-producing acceleration kernels for AgdaProver Stage 2.
//!
//! The ABI deliberately moves only finite numeric batches.  It never parses
//! Agda, invents proof evidence, or decides that a proposal is valid.  Python
//! retains the versioned IR and Agda independently validates every proposal.

use std::slice;

pub const ABI_VERSION: u32 = 3;

#[unsafe(no_mangle)]
pub extern "C" fn agdaprover_native_abi_version() -> u32 {
    ABI_VERSION
}

pub fn activate(value: f32) -> f32 {
    value.clamp(0.0, 1.0)
}

/// Score a CSR batch of sparse action deltas against one shared accumulator.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn agdaprover_nnue_score_batch(
    base_accumulator: *const f32,
    embeddings: *const f32,
    input_size: usize,
    hidden_size: usize,
    output_weights: *const f32,
    output_bias: f32,
    offsets: *const usize,
    indices: *const u32,
    values: *const f32,
    item_count: usize,
    nonzero_count: usize,
    output: *mut f32,
) -> i32 {
    if hidden_size == 0 || input_size == 0 {
        return -2;
    }
    if base_accumulator.is_null()
        || embeddings.is_null()
        || output_weights.is_null()
        || offsets.is_null()
        || output.is_null()
        || (nonzero_count != 0 && (indices.is_null() || values.is_null()))
    {
        return -1;
    }
    let Some(embedding_count) = input_size.checked_mul(hidden_size) else {
        return -6;
    };
    let base = unsafe { slice::from_raw_parts(base_accumulator, hidden_size) };
    let embeddings = unsafe { slice::from_raw_parts(embeddings, embedding_count) };
    let weights = unsafe { slice::from_raw_parts(output_weights, hidden_size) };
    let offsets = unsafe { slice::from_raw_parts(offsets, item_count + 1) };
    let indices = if nonzero_count == 0 {
        &[]
    } else {
        unsafe { slice::from_raw_parts(indices, nonzero_count) }
    };
    let values = if nonzero_count == 0 {
        &[]
    } else {
        unsafe { slice::from_raw_parts(values, nonzero_count) }
    };
    let output = unsafe { slice::from_raw_parts_mut(output, item_count) };
    if offsets.first().copied() != Some(0) || offsets.last().copied() != Some(nonzero_count) {
        return -3;
    }
    let mut accumulator = vec![0.0_f32; hidden_size];
    for item in 0..item_count {
        accumulator.copy_from_slice(base);
        let start = offsets[item];
        let end = offsets[item + 1];
        if start > end || end > nonzero_count {
            return -3;
        }
        for position in start..end {
            let feature = indices[position] as usize;
            if feature >= input_size || !values[position].is_finite() {
                return -4;
            }
            let embedding = &embeddings[feature * hidden_size..(feature + 1) * hidden_size];
            let scale = values[position];
            for hidden in 0..hidden_size {
                accumulator[hidden] += scale * embedding[hidden];
            }
        }
        let mut score = output_bias;
        for hidden in 0..hidden_size {
            score += weights[hidden] * activate(accumulator[hidden]);
        }
        if !score.is_finite() {
            return -5;
        }
        output[item] = score;
    }
    0
}
