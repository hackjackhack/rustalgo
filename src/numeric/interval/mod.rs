#[derive(Debug)]
pub struct Interval<T> {
    left: T,
    right: T,
    left_open: bool,
    right_open: bool,

    _norm_left: T,
    _norm_right: T
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

    pub fn new(left: T, right: T, left_open: bool, right_open: bool) -> Self {
        let mut _left_open = if left == Self::neg_inf() { true } else { left_open };
        let mut _right_open = if right == Self::pos_inf() { true } else { right_open };
        Self {
            left,
            right,
            left_open: _left_open,
            right_open: _right_open,
            _norm_left: Self::norm_left(left, _left_open),
            _norm_right: Self::norm_right(right, _right_open),
        }
    }
}

impl<T: PrimInt + Signed + ToString> std::fmt::Display for Interval<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}, {}{}",
                if self.left_open {'('} else {'['},
                if self.left == Self::neg_inf() { String::from("-INF") } else { self.left.to_string() },
                if self.right == Self::pos_inf() { String::from("+INF") } else { self.right.to_string() },
                if self.right_open {')'} else {']'})
    }
}

pub fn pos_inf_v<U: PrimInt>(_u: U) -> U { U::max_value() }
pub fn neg_inf_v<U: PrimInt>(_u: U) -> U { U::min_value() }

#[macro_export]
macro_rules! ITVL {
    [$x:expr, $y: expr] => { algorithm::numeric::interval::Interval::new($x, $y, false, false) };
    [$x:expr, $y: expr;] => { algorithm::numeric::interval::Interval::new($x, $y, false, true) };
    [;$x:expr, $y: expr] => { algorithm::numeric::interval::Interval::new($x, $y, true, false) };
    [;$x:expr, $y: expr;] => { algorithm::numeric::interval::Interval::new($x, $y, true, true) };
    [;,$x:expr] => { algorithm::numeric::interval::Interval::new(algorithm::numeric::interval::neg_inf_v($x), $x, true, false) };
    [;,$x:expr;] => { algorithm::numeric::interval::Interval::new(algorithm::numeric::interval::neg_inf_v($x), $x, true, true) };
    [$x:expr,;] => { algorithm::numeric::interval::Interval::new($x, algorithm::numeric::interval::pos_inf_v($x), false, true) };
    [;$x:expr,;] => { algorithm::numeric::interval::Interval::new($x, algorithm::numeric::interval::pos_inf_v($x), true, true) };
    [;;$ty:ty] => { algorithm::numeric::interval::Interval::new(<$ty>::min_value(), <$ty>::max_value(), true, true) };
}
