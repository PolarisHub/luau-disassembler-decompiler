//! A reimplementation of C's `printf("%.*g")` so that number/vector constants render
//! identically to `luau-compile --text` (which uses `%.17g` for numbers and `%.9g` for
//! vectors). Rust's native float formatting uses shortest round-trip, which differs, so we
//! match C's `%g` rules here to keep the disassembly diff-clean against the oracle.

/// Format `value` the way C's `%.*g` would, with `precision` significant digits.
pub fn format_g(value: f64, precision: usize) -> String {
    if value.is_nan() {
        return "nan".to_string();
    }
    if value.is_infinite() {
        return if value < 0.0 { "-inf" } else { "inf" }.to_string();
    }

    // C: precision 0 is treated as 1.
    let p = precision.max(1);

    // Determine the decimal exponent X as if formatted with %e at precision p-1.
    let sci = format!("{:.*e}", p - 1, value);
    let exp_x: i32 = sci
        .rsplit('e')
        .next()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);

    // %g chooses fixed notation when -4 <= X < P, else scientific.
    if exp_x >= -4 && exp_x < p as i32 {
        let frac_digits = (p as i32 - 1 - exp_x).max(0) as usize;
        let fixed = format!("{:.*}", frac_digits, value);
        strip_trailing_zeros(&fixed)
    } else {
        // Scientific: mantissa already has p-1 fractional digits in `sci`; strip zeros from
        // the mantissa and rewrite the exponent in C style (sign + >= 2 digits).
        let (mant, _) = sci.split_once('e').unwrap_or((sci.as_str(), "0"));
        let mant = strip_trailing_zeros(mant);
        let sign = if exp_x < 0 { '-' } else { '+' };
        format!("{mant}e{sign}{:02}", exp_x.unsigned_abs())
    }
}

/// Remove trailing zeros in the fractional part, then a dangling decimal point. Leaves a
/// number with no fractional part untouched (e.g. "1000000" stays "1000000").
fn strip_trailing_zeros(s: &str) -> String {
    if !s.contains('.') {
        return s.to_string();
    }
    let trimmed = s.trim_end_matches('0');
    trimmed.trim_end_matches('.').to_string()
}

#[cfg(test)]
mod tests {
    use super::format_g;

    #[test]
    fn matches_c_printf_g() {
        // Values cross-checked against printf("%.17g", x).
        assert_eq!(format_g(3.5, 17), "3.5");
        assert_eq!(format_g(1000000.0, 17), "1000000");
        assert_eq!(format_g(0.1, 17), "0.10000000000000001");
        assert_eq!(format_g(0.0, 17), "0");
        assert_eq!(format_g(-2.25, 17), "-2.25");
        assert_eq!(format_g(100.0, 17), "100");
        // very small / very large fall into scientific notation
        assert_eq!(format_g(1e-9, 9), "1e-09");
        assert_eq!(format_g(1.5e300, 17), "1.5e+300");
    }
}
