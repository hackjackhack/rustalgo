use algorithm::ITVL;
use algorithm::numeric::interval::Interval;

fn main() {
    let a = ITVL!(5, 10;);
    let b = ITVL!(;,1);
    let c = ITVL!(-1000,;);
    let d = ITVL!(;;i128);
    let e = ITVL!(0, 200);
    let f = Interval::new(5, 20, true, true);
    println!("{}", a);
    println!("{}", b);
    println!("{}", c);
    println!("{}", d);
    println!("{}", e);
    println!("{}", f);
}