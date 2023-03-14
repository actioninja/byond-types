//! A rusty utility crate for common BYOND types

use duplicate::duplicate_item;

/// A representation of the `Dir` type.
///
/// Enum discriminants are the same as the internal BYOND value, eg `North` = 1, `South` = 2, ...
///
/// `All` represents the special value created when all four cardinals are masked together
///
/// Implements both `From` and `Into` for all primitive numeric types
#[derive(Eq, PartialEq, Copy, Clone, Default, Debug)]
pub enum Dir {
    North = 1,
    #[default]
    South = 2,
    East = 4,
    West = 8,
    Southeast = 6,
    Southwest = 10,
    Northeast = 5,
    Northwest = 9,
    All = 15,
}

impl Dir {
    /// Returns an array of all 4 cardinal directions
    /// Order matches the order that Byond iterates Dirs in
    #[inline]
    #[must_use]
    pub const fn cardinals() -> [Self; 4] {
        [Self::South, Self::North, Self::East, Self::West]
    }

    /// Returns an array of all 4 diagonal directions
    /// Order matches the order that Byond iterates Dirs in
    #[inline]
    #[must_use]
    pub const fn diagonals() -> [Self; 4] {
        [
            Self::Southeast,
            Self::Southwest,
            Self::Northeast,
            Self::Northwest,
        ]
    }

    /// Returns an array of all 8 standard directions
    /// Order matches the order that Byond iterates Dirs in
    #[inline]
    #[must_use]
    pub const fn cardinals_and_diagonals() -> [Self; 8] {
        [
            Self::South,
            Self::North,
            Self::East,
            Self::West,
            Self::Southeast,
            Self::Southwest,
            Self::Northeast,
            Self::Northwest,
        ]
    }

    /// Returns true if the enum value is a cardinal, false otherwise
    #[must_use]
    #[inline]
    pub const fn is_cardinal(&self) -> bool {
        matches!(self, Self::South | Self::North | Self::East | Self::West)
    }

    /// Returns true if the enum value is a diagonal, false otherwise
    #[must_use]
    #[inline]
    pub const fn is_diagonal(&self) -> bool {
        matches!(
            self,
            Self::Southeast | Self::Southwest | Self::Northeast | Self::Northwest
        )
    }

    /// Combines two cardinal directions into a diagonal direction
    ///
    /// # Returns
    /// - `Some(Dir)` if the combination yields a valid diagonal
    /// - `None` if the combination is invalid:
    ///   - opposite directions (eg, `North` and `South`)
    ///   - diagonal with another direction
    ///   - `All` with anything
    #[must_use]
    pub const fn combine(self, x: Self) -> Option<Self> {
        match self {
            Self::North => match x {
                Self::East => Some(Self::Northeast),
                Self::West => Some(Self::Northwest),
                _ => None,
            },
            Self::South => match x {
                Self::East => Some(Self::Southeast),
                Self::West => Some(Self::Southwest),
                _ => None,
            },
            Self::East => match x {
                Self::North => Some(Self::Northeast),
                Self::South => Some(Self::Southeast),
                _ => None,
            },
            Self::West => match x {
                Self::North => Some(Self::Northwest),
                Self::South => Some(Self::Southwest),
                _ => None,
            },
            _ => None,
        }
    }

    /// Rotates a direction clockwise or counterclockwise by the number of degrees specified by `by` (direction depends
    /// on sign of `by`). Accepts arbitrarily large values, final direction is calculated from `by`
    ///
    /// Returns the new direction.
    ///
    /// Must always be called with a multiple of 45
    ///
    /// Prefer to use the `const` explicit variations of this function when possible as their evaluation is resolved further
    /// at compile time
    ///
    /// Special case: All always returns itself
    #[must_use]
    pub fn rotate(self, by: i32) -> Self {
        assert_eq!(by % 45, 0, "Rotation must be a multiple of 45 degrees");
        if Self::All == self {
            return self;
        }

        let mut dir = self;
        for _ in 0..by.abs() / 45 {
            dir = if by > 0 {
                dir.rotate_cw_45()
            } else {
                dir.rotate_ccw_45()
            };
        }
        dir
    }

    /// Rotates the direction clockwise by 45 degrees, returning the new direction
    ///
    /// This function is safe to chain (`.rotate_cw_45().rotate_cw_45()`) with no added performance cost due to its
    /// `const` evaluation
    ///
    /// Special case: All always returns itself
    #[must_use]
    pub const fn rotate_cw_45(self) -> Self {
        match self {
            Self::North => Self::Northeast,
            Self::South => Self::Southwest,
            Self::East => Self::Southeast,
            Self::West => Self::Northwest,
            Self::Southeast => Self::South,
            Self::Southwest => Self::West,
            Self::Northeast => Self::East,
            Self::Northwest => Self::North,
            Self::All => Self::All,
        }
    }

    /// Rotates the direction clockwise by 90 degrees, returning the new direction
    ///
    /// This function is safe to chain (`.rotate_cw_90().rotate_cw_90()) with no added performance cost due to its
    /// `const` evaluation
    ///
    /// Special case: All always returns itself
    #[must_use]
    pub const fn rotate_cw_90(self) -> Self {
        match self {
            Self::North => Self::East,
            Self::South => Self::West,
            Self::East => Self::South,
            Self::West => Self::North,
            Self::Southeast => Self::Southwest,
            Self::Southwest => Self::Northwest,
            Self::Northeast => Self::Southeast,
            Self::Northwest => Self::Northeast,
            Self::All => Self::All,
        }
    }

    /// Rotates the direction clockwise by 45 degrees, returning the new direction
    ///
    /// This function is safe to chain (`.rotate_cw_45().rotate_cw_45()) with no added performance cost due to its
    /// `const` evaluation
    ///
    /// Special case: All always returns itself
    #[must_use]
    pub const fn rotate_ccw_45(self) -> Self {
        match self {
            Self::North => Self::Northwest,
            Self::South => Self::Southeast,
            Self::East => Self::Northeast,
            Self::West => Self::Southwest,
            Self::Southeast => Self::East,
            Self::Southwest => Self::South,
            Self::Northeast => Self::North,
            Self::Northwest => Self::West,
            Self::All => Self::All,
        }
    }

    /// Rotates the direction counterclockwise by 90 degrees, returning the new direction
    ///
    /// This function is safe to chain (`.rotate_ccw_90().rotate_ccw_90()) with no added performance cost due to its
    /// `const` evaluation
    ///
    /// Special case: All always returns itself
    #[must_use]
    pub const fn rotate_ccw_90(self) -> Self {
        match self {
            Self::North => Self::West,
            Self::South => Self::East,
            Self::East => Self::North,
            Self::West => Self::South,
            Self::Southeast => Self::Northeast,
            Self::Southwest => Self::Southeast,
            Self::Northeast => Self::Northwest,
            Self::Northwest => Self::Southwest,
            Self::All => Self::All,
        }
    }
}

#[duplicate_item(
number_type;
[ u8 ]; [ u16 ]; [ u32 ]; [ u64 ]; [ u128 ]; [ usize ];
[ i8 ]; [ i16 ]; [ i32 ]; [ i64 ]; [ i128 ]; [ isize ];
)]
mod number_conversions {
    use crate::Dir;

    impl TryFrom<number_type> for Dir {
        type Error = ();

        fn try_from(value: number_type) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Self::North),
                2 => Ok(Self::South),
                4 => Ok(Self::East),
                8 => Ok(Self::West),
                _ => Err(()),
            }
        }
    }

    impl From<Dir> for number_type {
        fn from(value: Dir) -> number_type {
            value as number_type
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Dir;

    #[test]
    fn dir_rotations() {
        // rotating clockwise then counterclockwise by the same value yields the same dir for all dirs
        for dir in Dir::cardinals_and_diagonals() {
            assert_eq!(dir.rotate_cw_45().rotate_ccw_45(), dir);
            assert_eq!(dir.rotate_cw_90().rotate_ccw_90(), dir);
        }

        // clockwise rotations
        assert_eq!(Dir::North.rotate_cw_45(), Dir::Northeast);
        assert_eq!(Dir::North.rotate_cw_90(), Dir::East);
        assert_eq!(Dir::North.rotate_cw_45().rotate_cw_45(), Dir::East);
        assert_eq!(
            Dir::North.rotate_cw_45().rotate_cw_45(),
            Dir::North.rotate_cw_90()
        );
        assert_eq!(Dir::North.rotate_cw_90().rotate_cw_90(), Dir::South);

        // counterclockwise rotations
        assert_eq!(Dir::North.rotate_ccw_45(), Dir::Northwest);
        assert_eq!(Dir::North.rotate_ccw_90(), Dir::West);
        assert_eq!(Dir::North.rotate_ccw_45().rotate_ccw_45(), Dir::West);
        assert_eq!(
            Dir::North.rotate_ccw_45().rotate_ccw_45(),
            Dir::North.rotate_ccw_90()
        );
        assert_eq!(Dir::North.rotate_ccw_90().rotate_ccw_90(), Dir::South);

        // arbitrary values in `rotate` function yield correct results
        assert_eq!(Dir::North.rotate(180), Dir::South);
        assert_eq!(Dir::North.rotate(-180), Dir::South);
        assert_eq!(Dir::North.rotate(90), Dir::East);
        assert_eq!(Dir::North.rotate(-90), Dir::West);
        assert_eq!(Dir::North.rotate(45), Dir::Northeast);
        assert_eq!(Dir::North.rotate(-45), Dir::Northwest);
        assert_eq!(Dir::North.rotate(135), Dir::Southeast);
        assert_eq!(Dir::North.rotate(-135), Dir::Southwest);
    }

    #[test]
    fn dir_combination() {
        // correct combinations that yield a Some diagonal
        let valid_pairs = [
            (Dir::North, Dir::West, Dir::Northwest),
            (Dir::North, Dir::East, Dir::Northeast),
            (Dir::South, Dir::West, Dir::Southwest),
            (Dir::South, Dir::East, Dir::Southeast),
        ];

        for (x, y, result) in valid_pairs {
            assert_eq!(x.combine(y), Some(result));
            // associativity
            assert_eq!(y.combine(x), Some(result));
        }

        // incorrect combos that yield a None
        // opposites
        assert_eq!(Dir::West.combine(Dir::East), None);
        assert_eq!(Dir::North.combine(Dir::South), None);
        // any combination with a diagonal
        for x in Dir::diagonals() {
            for y in Dir::cardinals_and_diagonals() {
                assert_eq!(x.combine(y), None);
            }
        }

        // all with anything
        for x in Dir::cardinals_and_diagonals() {
            assert_eq!(Dir::All.combine(x), None);
            assert_eq!(x.combine(Dir::All), None);
        }
    }
}
