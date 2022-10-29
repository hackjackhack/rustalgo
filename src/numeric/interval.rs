#[derive(Debug)]
pub struct Interval<T> {
    left: T,
    right: T,
    left_open: bool,
    right_open: bool,
}

use num::PrimInt;
use num::Signed;
impl<T: PrimInt + Signed> Interval<T> {
    fn pos_inf() -> T { T::max_value() }
    fn neg_inf() -> T { T::min_value() }
    fn norm_left(left: T, left_open: bool) -> T {
        if left == Self::neg_inf() { left }
        else if left_open { left + T::one() } else { left }
    }
    fn norm_right(right: T, right_open: bool) -> T {
        if right == Self::pos_inf() { right }
        else if !right_open { right + T::one() } else { right }
    }
    fn unnorm_left(&self) -> T {
        if self.left == Self::neg_inf() { self.left }
        else if self.left_open { self.left - T::one() } else { self.left }
    }
    fn unnorm_right(&self) -> T {
        if self.right == Self::pos_inf() { self.right }
        else if self.right_open { self.right } else { self.right - T::one() }
    }

    pub fn new(left: T, right: T, left_open: bool, right_open: bool) -> Self {
        let mut _left_open = if left == Self::neg_inf() { true } else { left_open };
        let mut _right_open = if right == Self::pos_inf() { true } else { right_open };
        Self {
            left: Self::norm_left(left, _left_open),
            right: Self::norm_right(right, _right_open),
            left_open: _left_open,
            right_open: _right_open
        }
    }
    pub fn left(&self) -> T { self.unnorm_left() }
    pub fn right(&self) -> T { self.unnorm_right() }
    pub fn is_left_open(&self) -> bool { self.left_open }
    pub fn is_right_open(&self) -> bool { self.right_open }
    pub fn is_finite(&self) -> bool { self.left != Self::neg_inf() && self.right != Self::pos_inf() }
    pub fn is_empty(&self) -> bool { self.is_finite() && self.right <= self.left }
    pub fn size(&self) -> Option<u128> {
        if self.is_finite() {
            if self.is_empty() { Some(0) } else {
                let l = self.left.to_i128().expect("Interval left cannot be converted to i128");
                let r = self.right.to_i128().expect("Interval right cannot be converted to i128");
                Some(r.abs_diff(l))
            }
        } else {
            None
        }
    }
    pub fn extend_right(&mut self, addend: T) -> Result<&Self, &'static str> {
        self.right = self.right.saturating_add(addend);
        if self.right < Self::pos_inf() { Ok(self) } else { Err("Upper-bound cracks") }
    }
    pub fn extend_left(&mut self, addend: T) -> Result<&Self, &'static str> {
        self.left = self.left.saturating_sub(addend);
        if self.left > Self::neg_inf() { Ok(self) } else { Err("Lower-bound cracks") }
    }

}

impl<T: PrimInt + Signed> PartialEq for Interval<T> {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.right == other.right
    }
}

impl<T: PrimInt + Signed + ToString> std::fmt::Display for Interval<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}, {}{}",
                if self.left_open {'('} else {'['},
                if self.left == Self::neg_inf() { String::from("-INF") } else { self.unnorm_left().to_string() },
                if self.right == Self::pos_inf() { String::from("+INF") } else { self.unnorm_right().to_string() },
                if self.right_open {')'} else {']'})
    }
}

pub fn pos_inf_v<U: PrimInt>(_u: U) -> U { U::max_value() }
pub fn neg_inf_v<U: PrimInt>(_u: U) -> U { U::min_value() }

#[macro_export]
macro_rules! ITVL {
    [$x:expr, $y: expr] => { $crate::numeric::interval::Interval::new($x, $y, false, false) };
    [$x:expr, $y: expr;] => { $crate::numeric::interval::Interval::new($x, $y, false, true) };
    [;$x:expr, $y: expr] => { $crate::numeric::interval::Interval::new($x, $y, true, false) };
    [;$x:expr, $y: expr;] => { $crate::numeric::interval::Interval::new($x, $y, true, true) };
    [;,$x:expr] => { $crate::numeric::interval::Interval::new($crate::numeric::interval::neg_inf_v($x), $x, true, false) };
    [;,$x:expr;] => { $crate::numeric::interval::Interval::new($crate::numeric::interval::neg_inf_v($x), $x, true, true) };
    [$x:expr,;] => { $crate::numeric::interval::Interval::new($x, $crate::numeric::interval::pos_inf_v($x), false, true) };
    [;$x:expr,;] => { $crate::numeric::interval::Interval::new($x, $crate::numeric::interval::pos_inf_v($x), true, true) };
    [;;$ty:ty] => { $crate::numeric::interval::Interval::new(<$ty>::min_value(), <$ty>::max_value(), true, true) };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_creation() {
        let _a = ITVL!(5, 10;);
        let _b = ITVL!(;,1);
        let _c = ITVL!(-1000,;);
        let _d = ITVL!(;;i128);
        let _e = ITVL!(0, 200);
        let _f = Interval::new(5, 20, true, true);
    }

    #[test]
    fn test_display() {
        let a = ITVL!(5, 10;);
        let b = ITVL!(;,1);
        let c = ITVL!(-1000,;);
        let d = ITVL!(;;i128);
        let e = ITVL!(0, 200);
        let f = Interval::new(5, 20, true, true);
        assert_eq!("[5, 10)", a.to_string());
        assert_eq!("(-INF, 1]", b.to_string());
        assert_eq!("[-1000, +INF)", c.to_string());
        assert_eq!("(-INF, +INF)", d.to_string());
        assert_eq!("[0, 200]", e.to_string());
        assert_eq!("(5, 20)", f.to_string());
    }

    #[test]
    fn test_equality() {
        assert_eq!(ITVL!(5, 10), ITVL!(5, 10));
        assert_eq!(ITVL!(5, 10), ITVL!(;4, 11;));
        assert_eq!(ITVL!(;-10, 10;), ITVL!(-9, 9));
        assert_eq!(ITVL!(;, 10), ITVL!(;, 11;));
        assert_eq!(ITVL!(;4, 11;), ITVL!(5, 10));
    }

    #[test]
    fn test_empty_finite() {
        let a = ITVL!(5, 10;);
        let b = ITVL!(;,1);
        let c = ITVL!(-1000,;);
        let d = ITVL!(;;i128);
        let e = ITVL!(0, 200);
        let f = Interval::new(5, 20, true, true);
        let g = ITVL!(200, 200);
        let h = ITVL!(200, 199);
        assert!(a.is_finite());
        assert!(!a.is_empty());
        assert!(!b.is_finite());
        assert!(!b.is_empty());
        assert!(!c.is_finite());
        assert!(!c.is_empty());
        assert!(!d.is_finite());
        assert!(!d.is_empty());
        assert!(e.is_finite());
        assert!(!e.is_empty());
        assert!(f.is_finite());
        assert!(!f.is_empty());
        assert!(g.is_finite());
        assert!(!g.is_empty());
        assert!(h.is_finite());
        assert!(h.is_empty());
    }

    #[test]
    fn test_size() {
        let a = ITVL!(5, 10;);
        let b = ITVL!(;,1);
        let c = ITVL!(-1000,;);
        let d = ITVL!(;;i128);
        let e = ITVL!(0, 200);
        let f = Interval::new(5, 20, true, true);
        let g = ITVL!(200, 200);
        let h = ITVL!(200, 199);
        let i = ITVL!(200, -11);
        assert_eq!(5, a.size().unwrap());
        assert!(b.size().is_none());
        assert!(c.size().is_none());
        assert!(d.size().is_none());
        assert_eq!(201, e.size().unwrap());
        assert_eq!(14, f.size().unwrap());
        assert_eq!(1, g.size().unwrap());
        assert_eq!(0, h.size().unwrap());
        assert_eq!(0, i.size().unwrap());
    }

    #[test]
    fn test_extend() {
        let mut a = ITVL!(5, 10);
        assert!(a.extend_right(10).is_ok());
        assert!(a.extend_left(10).is_ok());
        assert_eq!(ITVL!(-5, 20), a);

        let mut b = ITVL!(-127i8, 126i8);
        assert!(b.extend_right(1).is_err());
        assert!(b.extend_left(1).is_err());
        assert_eq!(ITVL!(;;i8), b);
    }
}
