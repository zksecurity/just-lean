use std::time::Instant;

fn gen(n: usize, seed: u64) -> Vec<u64> {
    let mut s = seed; let mut v = Vec::with_capacity(n);
    for _ in 0..n { s ^= s >> 12; s ^= s << 25; s ^= s >> 27; v.push(s.wrapping_mul(0x2545F4914F6CDD1D)); }
    v
}

/// Idiomatic bottom-up merge sort with a scratch buffer, safe Rust, bounds-checked slices.
fn merge_runs(src: &[u64], dst: &mut [u64], lo: usize, mid: usize, hi: usize) {
    let (mut i, mut j) = (lo, mid);
    for k in lo..hi {
        if i < mid && (j >= hi || src[i] <= src[j]) { dst[k] = src[i]; i += 1; }
        else { dst[k] = src[j]; j += 1; }
    }
}
/// Same bottom-up sort with unchecked indexing (no bounds checks), to match Lean's proof-elided version.
fn merge_runs_unchecked(src: &[u64], dst: &mut [u64], lo: usize, mid: usize, hi: usize) {
    let (mut i, mut j) = (lo, mid);
    for k in lo..hi {
        unsafe {
            if i < mid && (j >= hi || *src.get_unchecked(i) <= *src.get_unchecked(j)) { *dst.get_unchecked_mut(k) = *src.get_unchecked(i); i += 1; }
            else { *dst.get_unchecked_mut(k) = *src.get_unchecked(j); j += 1; }
        }
    }
}
fn bottom_up_unchecked(v: &mut Vec<u64>) {
    let n = v.len();
    let mut src = std::mem::take(v);
    let mut dst = vec![0u64; n];
    let mut width = 1;
    while width < n {
        let mut lo = 0;
        while lo < n {
            let mid = (lo + width).min(n);
            let hi = (lo + 2 * width).min(n);
            merge_runs_unchecked(&src, &mut dst, lo, mid, hi);
            lo += 2 * width;
        }
        std::mem::swap(&mut src, &mut dst);
        width *= 2;
    }
    *v = src;
}
/// Bottom-up with a branchless merge step (same trick as the Lean version).
fn merge_runs_branchless(src: &[u64], dst: &mut [u64], lo: usize, mid: usize, hi: usize) {
    let (mut i, mut j) = (lo, mid);
    let mut k = lo;
    while k < hi {
        if i < mid && j < hi {
            let x = src[i]; let y = src[j];
            let take_left = x <= y;
            dst[k] = if take_left { x } else { y };
            i += take_left as usize;
            j += (!take_left) as usize;
        } else if i < mid { dst[k] = src[i]; i += 1; }
        else { dst[k] = src[j]; j += 1; }
        k += 1;
    }
}
fn bottom_up_branchless(v: &mut Vec<u64>) {
    let n = v.len();
    let mut src = std::mem::take(v);
    let mut dst = vec![0u64; n];
    let mut width = 1;
    while width < n {
        let mut lo = 0;
        while lo < n {
            let mid = (lo + width).min(n);
            let hi = (lo + 2 * width).min(n);
            merge_runs_branchless(&src, &mut dst, lo, mid, hi);
            lo += 2 * width;
        }
        std::mem::swap(&mut src, &mut dst);
        width *= 2;
    }
    *v = src;
}
fn bottom_up(v: &mut Vec<u64>) {
    let n = v.len();
    let mut src = std::mem::take(v);
    let mut dst = vec![0u64; n];
    let mut width = 1;
    while width < n {
        let mut lo = 0;
        while lo < n {
            let mid = (lo + width).min(n);
            let hi = (lo + 2 * width).min(n);
            merge_runs(&src, &mut dst, lo, mid, hi);
            lo += 2 * width;
        }
        std::mem::swap(&mut src, &mut dst);
        width *= 2;
    }
    *v = src;
}

/// Idiomatic top-down merge sort (recursive), copies runs out via a temp buffer.
fn top_down(v: &mut [u64], buf: &mut Vec<u64>) {
    let n = v.len();
    if n <= 1 { return; }
    let mid = n / 2;
    let (l, r) = v.split_at_mut(mid);
    top_down(l, buf); top_down(r, buf);
    buf.clear(); buf.extend_from_slice(l);
    let (mut i, mut j, mut k) = (0, mid, 0);
    while i < mid && j < n {
        if buf[i] <= v[j] { v[k] = buf[i]; i += 1; } else { v[k] = v[j]; j += 1; }
        k += 1;
    }
    while i < mid { v[k] = buf[i]; i += 1; k += 1; }
}

/// Top-down ping-pong merge sort in one buffer of length 2n (same algorithm as Lean V10).
fn pp_merge(a: &mut [u64], s: usize, d: usize, mid: usize, hi: usize, mut i: usize, mut j: usize, mut k: usize) {
    while k < hi {
        if i < mid && (j >= hi || a[s + i] <= a[s + j]) { a[d + k] = a[s + i]; i += 1; }
        else { a[d + k] = a[s + j]; j += 1; }
        k += 1;
    }
}
fn pp_sort_range(a: &mut [u64], s: usize, d: usize, lo: usize, hi: usize) {
    // precondition: a[s+lo..s+hi] == a[d+lo..d+hi]; postcondition: a[d+lo..d+hi] sorted
    if hi - lo <= 1 { return; }
    let mid = lo + (hi - lo) / 2;
    pp_sort_range(a, d, s, lo, mid);
    pp_sort_range(a, d, s, mid, hi);
    pp_merge(a, s, d, mid, hi, lo, mid, lo);
}
fn ping_pong(v: &mut Vec<u64>) {
    let n = v.len();
    let mut a = vec![0u64; 2 * n];
    a[..n].copy_from_slice(v);
    a[n..].copy_from_slice(v);
    pp_sort_range(&mut a, 0, n, 0, n);
    v.copy_from_slice(&a[n..]);
}

/// Bidirectional branchless merge of two equal-length runs src[lo..mid) and src[mid..hi) into dst.
fn merge_bidi(src: &[u64], dst: &mut [u64], lo: usize, mid: usize, hi: usize) {
    let w = mid - lo;
    let (mut i, mut j, mut k) = (lo, mid, lo);
    let (mut ib, mut jb, mut kb) = (mid, hi, hi);
    for _ in 0..w {
        let x = src[i]; let y = src[j];
        let tl = x <= y;
        dst[k] = if tl { x } else { y };
        i += tl as usize; j += (!tl) as usize; k += 1;
        let xb = src[ib - 1]; let yb = src[jb - 1];
        let tr = xb <= yb;
        dst[kb - 1] = if tr { yb } else { xb };
        ib -= (!tr) as usize; jb -= tr as usize; kb -= 1;
    }
}
fn merge_kernel(src: &[u64], dst: &mut [u64], lo: usize, mid: usize, hi: usize) {
    if mid - lo == hi - mid && lo < mid { merge_bidi(src, dst, lo, mid, hi) } else { merge_runs_branchless(src, dst, lo, mid, hi) }
}
fn pass(src: &[u64], dst: &mut [u64], w: usize, lo: usize, hi: usize) {
    let mut cur = lo;
    while cur < hi {
        let mid = (cur + w).min(hi);
        let hi2 = (cur + 2 * w).min(hi);
        merge_kernel(src, dst, cur, mid, hi2);
        cur += 2 * w;
    }
}
/// bidirectional + cache-blocked (B = 2^14, passes in pairs so data returns to `src`)
fn bidi_blocked(v: &mut Vec<u64>) {
    let n = v.len();
    let b = 16384usize;
    let mut src = std::mem::take(v);
    let mut dst = vec![0u64; n];
    let mut lo = 0;
    while lo < n {
        let hi = (lo + b).min(n);
        let mut w = 1;
        while w < b {
            pass(&src, &mut dst, w, lo, hi);
            pass(&dst, &mut src, 2 * w, lo, hi);
            w *= 4;
        }
        lo += b;
    }
    let mut w = b;
    while w < n {
        pass(&src, &mut dst, w, 0, n);
        std::mem::swap(&mut src, &mut dst);
        w *= 2;
    }
    *v = src;
}

fn timeit(label: &str, xs: &Vec<u64>, f: impl FnOnce(&mut Vec<u64>)) {
    let mut a = xs.clone();
    let t = Instant::now(); f(&mut a); let dt = t.elapsed().as_micros();
    let mut r = xs.clone(); r.sort_unstable();
    assert!(a == r, "{label}: WRONG RESULT");
    println!("{label}: {} ms", dt as f64 / 1000.0);
}

fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
    let xs = gen(n, 42);
    println!("n = {n}");
    timeit("rust bottom-up merge sort (plain)", &xs, |a| bottom_up(a));
    timeit("rust bottom-up merge sort (unchecked idx)", &xs, |a| bottom_up_unchecked(a));
    timeit("rust bottom-up, branchless merge   ", &xs, |a| bottom_up_branchless(a));
    timeit("rust top-down merge sort (plain) ", &xs, |a| { let mut b = Vec::new(); top_down(a, &mut b) });
    timeit("rust top-down ping-pong 2n (= Lean V10)", &xs, |a| ping_pong(a));
    timeit("rust bidirectional + blocked (= Lean sortBlocked)", &xs, |a| bidi_blocked(a));
    let mut pre = xs.clone(); pre.sort();
    timeit("rust Vec::sort on presorted input  ", &pre, |a| a.sort());
    timeit("rust Vec::sort (driftsort)       ", &xs, |a| a.sort());
    timeit("rust Vec::sort_unstable (ipnsort)", &xs, |a| a.sort_unstable());
}
