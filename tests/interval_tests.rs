use algorithm::{ITVL, numeric::interval::Interval};

#[test]
fn meeting_timeslots() {
    #[derive(Debug)]
    enum Day { Sun, Mon, Tue, Wed, Thr, Fri, Sat }
    impl Day {
        pub fn from_i16(value: i16) -> Self {
            match value / 24 {
                0 => Day::Sun,
                1 => Day::Mon,
                2 => Day::Tue,
                3 => Day::Wed,
                4 => Day::Thr,
                5 => Day::Fri,
                6 => Day::Sat,
                _ => panic!("Illegal day")
            }
        }
    }
    impl std::fmt::Display for Day {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    struct Timeslot {
        timeslots: Vec<Interval<i16>>
    }
    impl Timeslot {
        pub fn new() -> Self { Timeslot{ timeslots: vec![] } }
        pub fn add_slot(&mut self, day: Day, start_hour: i16, end_hour: i16) {
            self.timeslots.push(ITVL!((day as i16) * 24 + start_hour, (day as i16) * 24 + end_hour;))
        }
        pub fn intersect(&self, other: &Self) -> Timeslot {
            let mut out = Timeslot::new();
            for itvl1 in &self.timeslots {
                for itvl2 in &other.timeslots {
                    let common = itvl1.intersect(&itvl2);
                    if common.is_some() {
                        out.timeslots.push(common.unwrap());
                    }
                }
            }
            out
        }
    }
    impl std::fmt::Display for Timeslot {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let mut s: String = String::new();
            for itvl in &self.timeslots {
                s += format!("{}: {}-{}\n", Day::from_i16(itvl.normed_left()), itvl.normed_left() % 24, itvl.normed_right() % 24).as_str();
            }
            write!(f, "{}", s)
        }
    }
    
    let mut jack = Timeslot::new();
    jack.add_slot(Day::Mon, 8, 10);
    jack.add_slot(Day::Mon, 13, 15);
    jack.add_slot(Day::Wed, 11, 12);
    jack.add_slot(Day::Wed, 17, 18);
    jack.add_slot(Day::Thr, 13, 17);
    jack.add_slot(Day::Fri, 9, 12);

    let mut rick = Timeslot::new();
    rick.add_slot(Day::Mon, 17, 18);
    rick.add_slot(Day::Mon, 13, 15);
    rick.add_slot(Day::Wed, 17, 18);
    rick.add_slot(Day::Thr, 15, 16);
    rick.add_slot(Day::Fri, 11, 12);

    let mut mary = Timeslot::new();
    mary.add_slot(Day::Mon, 13, 14);
    mary.add_slot(Day::Tue, 9, 12);
    mary.add_slot(Day::Wed, 9, 18);
    mary.add_slot(Day::Thr, 10, 12);
    mary.add_slot(Day::Fri, 11, 13);
    
    assert_eq!("Mon: 13-15\nWed: 17-18\nThr: 15-16\nFri: 11-12\n", jack.intersect(&rick).to_string());
    assert_eq!("Mon: 13-14\nWed: 11-12\nWed: 17-18\nFri: 11-12\n", jack.intersect(&mary).to_string());
    assert_eq!("Mon: 13-14\nWed: 17-18\nFri: 11-12\n", jack.intersect(&rick).intersect(&mary).to_string());
}