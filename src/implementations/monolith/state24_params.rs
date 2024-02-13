
use crate::field::mersenne::MersenneField;
use crate::implementations::monolith::state24_params::monolith_mds_24::mds_multiply_u64;
use crate::implementations::monolith::{Monolith, LOOKUP_BITS, N_ROUNDS};
use crate::field::traits::field::Field;

impl Monolith<24> for MersenneField {
    const ROUND_CONSTANTS: [[u32; 24]; N_ROUNDS + 1] = match LOOKUP_BITS {
        // Seed is Monolith\x18\x06\xff\xff\xff\x7f\x08\x08\x08\x07
        8 => [
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [1821280327,1805192324,127749067,534494027,504066389,661859220,1964605566,11087311,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [939676630,132824540,1081150345,1901266162,1248854474,722216947,711899879,991065584,872971327,1747874412,889258434,857014393,1145792277,329607215,1069482641,1809464251,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [1792923486,1071073386,2086334655,615259270,1680936759,2069228098,679754665,598972355,1448263353,2102254560,1676515281,1529495635,981915006,436108429,1959227325,1710180674,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [814766386,746021429,758709057,1777861169,1875425297,1630916709,180204592,1301124329,307222363,297236795,866482358,1784330946,1841790988,1855089478,2122902104,1522878966,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [1132611924,1823267038,539457094,934064219,561891167,1325624939,1683493283,1582152536,851185378,1187215684,1520269176,801897118,741765053,1300119213,1960664069,1633755961,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ],
        // Seed is Monolith\x18\x06\xff\xff\xff\x7f\x10\x0f
        16 => [
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [769346737,166917339,604440681,55971328,2065847361,1291194722,1063146836,1387787161,262947647,1511147363,376158787,397578545,1294431154,1873712341,1079035183,500776250,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [1344367226,922651917,695054464,1087745069,285923125,2105564937,794831433,754054329,1047867365,1382672139,1054770276,1331170190,554335250,1985584177,1295206484,784794291,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [102062620,1175184551,479602980,1770539291,1067190863,582530175,1606750625,1111663835,1451190220,2794489,1859002505,138256978,1449379860,834348281,1599433907,1092961389,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [690755091,753017706,1989753436,675855470,1389440606,1525255759,491316739,829043290,1236089820,885268885,1459526211,965103410,537425277,1575772908,1611083284,1299721512,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [2137339913,1377046313,593161859,737352741,1908466467,637909385,967379091,740090396,1104689081,1638662606,1307664559,3856176,1335571944,1495612078,995877140,1772790623,1178584041,412585466,2078905810,549234502,1181028407,363220519,1649192353,895839514],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        ],
        _ => panic!("Unsupported lookup size"),
    };

    // THIS IS NOT MDS MATRIX! WAITING FOR THE CIRCULANT MDS MATRIX 24X24 TO BE PUBLISHED
    const MDS: [[u32; 24]; 24] = [
        [4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68],
        [68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16],
        [16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64],
        [64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60],
        [60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512],
        [512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096],
        [4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536],
        [65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4],
        [4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48],
        [48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36],
        [36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28],
        [28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128],
        [128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144],
        [262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768],
        [32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384, 32],
        [32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4, 16384],
        [16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20, 4],
        [4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12, 20],
        [20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16, 12],
        [12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4, 16],
        [16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4, 4],
        [4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8, 4],
        [4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4, 8],
        [8, 4, 4, 16, 12, 20, 4, 16384, 32, 32768, 262144, 128, 28, 36, 48, 4, 65536, 4096, 512, 60, 64, 16, 68, 4],
    ];

    const M_POWERS: [[u32; 24]; 24] = [
        [7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8],
        [8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21],
        [21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22],
        [22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6],
        [6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7],
        [7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9],
        [9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10],
        [10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13],
        [13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26],
        [26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8],
        [8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23],
        [23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7],
        [7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8],
        [8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21],
        [21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22],
        [22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6],
        [6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7],
        [7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9],
        [9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10],
        [10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13],
        [13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26],
        [26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8],
        [8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23],
        [23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8, 7],
    ];

    const MDS_FIELD: [[Self; 24]; 24] = const {
        let mut result = [[Self::ONE; 24]; 24];
        let mut i = 0;
        while i < 24 {
            let mut j = 0;
            while j < 24 {
                result[i][j] = Self(Self::MDS[i][j]);
                j += 1;
            }
            i += 1;
        }
    
        result
    };
    const ROUND_CONSTANTS_FIELD: [[Self; 24]; N_ROUNDS + 1] = const {
        let mut result = [[Self::ONE; 24]; N_ROUNDS + 1];
        let mut i = 0;
        while i < N_ROUNDS + 1 {
            let mut j = 0;
            while j < 24 {
                result[i][j] = Self(Self::ROUND_CONSTANTS[i][j]);
                j += 1;
            }
            i += 1;
        }
    
        result
    };

    // #[cfg(feature = "default-sponge-params")]
    fn concrete_u64(state_u64: &mut [u64; 24], round_constants: &[u32; 24]) {
        // println!("this is concrete_u64 in frequency domain");
        mds_multiply_u64(state_u64, round_constants)
    }
}

mod monolith_mds_24 {
    // use crate::monolith_hash::split;
    // use plonky2::field::goldilocks_field::GoldilocksField;
    // use plonky2::field::types::Field;

    use crate::field::mersenne::MersenneField;

    /// This module contains helper functions as well as constants used to perform a 12x12 vector-matrix
    /// multiplication. The special form of our MDS matrix i.e. being circulant, allows us to reduce
    /// the vector-matrix multiplication to a Hadamard product of two vectors in "frequency domain".
    /// This follows from the simple fact that every circulant matrix has the columns of the discrete
    /// Fourier transform matrix as orthogonal eigenvectors.
    /// The implementation also avoids the use of 3-point FFTs, and 3-point iFFTs, and substitutes that
    /// with explicit expressions. It also avoids, due to the form of our matrix in the frequency domain,
    /// divisions by 2 and repeated modular reductions. This is because of our explicit choice of
    /// an MDS matrix that has small powers of 2 entries in frequency domain.
    /// The following implementation has benefited greatly from the discussions and insights of
    /// Hamish Ivey-Law and Jacqueline Nabaglo of Polygon Zero.
    /// The circulant matrix is identified by its first row: [2097152, 3, 32, 8, 2048, 4, 32768, 1, 16, 512, 2, 1, 131072, 1, 1, 2].

    // MDS matrix in frequency domain.
    // More precisely, this is the output of the three 4-point (real) FFTs of the first column of
    // the MDS matrix i.e. just before the multiplication with the appropriate twiddle factors
    // and application of the final four 3-point FFT in order to get the full 12-point FFT.
    // The entries have been scaled appropriately in order to avoid divisions by 2 in iFFT2 and iFFT4.
    // The code to generate the matrix in frequency domain is based on an adaptation of a code, to generate
    // MDS matrices efficiently in original domain, that was developed by the Polygon Zero team.
    // const MDS_FREQ_BLOCK_ONE: [i64; 4] = [557572, 130, 8200, 3];
    // const MDS_FREQ_BLOCK_TWO: [(i64, i64); 4] = [(1048568, 64512), (-254, -1), (15, -16383), (3, 0)];
    // const MDS_FREQ_BLOCK_THREE: [i64; 4] = [491012, 127, -8183, 1];
    const MDS_FREQ_BLOCK_ONE: [i64; 6] = [1062, 81940, 8201, 37, 4121, 138];
    const MDS_FREQ_BLOCK_TWO: [(i64, i64); 6] = [(-62, -2038), (-131038, -32762), (-16376, 6), (16, -22), (-8162, -16), (254, -10)];
    const MDS_FREQ_BLOCK_THREE: [i64; 6] = [-996, 49166, 8191, 11, 4101, 120];

    pub(crate) fn mds_multiply_u64(state: &mut [u64; 24], round_constants: &[u32; 24]) {

        let mut state_freq = mds_multiply_freq(*state);

        for r in 0..24 {
            // Both have less than 40 bits
            state_freq[r] += round_constants[r] as u64;
            (*state)[r] = MersenneField::from_negative_u64_with_reduction(state_freq[r]).0 as u64;
        }

    }

    // We use split 3 x 4 FFT transform in order to transform our vectors into the frequency domain.
    #[inline(always)]
    pub(crate) fn mds_multiply_freq(state: [u64; 24]) -> [u64; 24] {
        let [s0, s1, s2, s3, s4, s5, s6, s7, 
            s8, s9, s10, s11, s12, s13, s14, s15,
            s16, s17, s18, s19, s20, s21, s22, s23] = state;

        let (u0, u1, u2) = fft4_real([s0, s6, s12, s18]);
        let (u4, u5, u6) = fft4_real([s1, s7, s13, s19]);
        let (u8, u9, u10) = fft4_real([s2, s8, s14, s20]);
        let (u12, u13, u14) = fft4_real([s3, s9, s15, s21]);
        let (u16, u17, u18) = fft4_real([s4, s10, s16, s22]);
        let (u20, u21, u22) = fft4_real([s5, s11, s17, s23]);

        let order = MersenneField::ORDER as u64;
        let mut t = [u0 as u64, u4 as u64, u8 as u64, u12 as u64, u16 as u64, u20 as u64];
        for (u, ur) in [u0 as u64, u4 as u64, u8 as u64, u12 as u64, u16 as u64, u20 as u64].iter().zip(t.iter_mut()) {
            *ur = MersenneField::from_u64_with_reduction((*u).try_into().unwrap()).0 as u64;
        }

        let ur0 = t[0] as i64;
        let ur4 = t[1] as i64;
        let ur8 = t[2] as i64;
        let ur12 = t[3] as i64;
        let ur16 = t[4] as i64;
        let ur20 = t[5] as i64;

        // This where the multiplication in frequency domain is done. More precisely, and with
        // the appropriate permuations in between, the sequence of
        // 3-point FFTs --> multiplication by twiddle factors --> Hadamard multiplication -->
        // 3 point iFFTs --> multiplication by (inverse) twiddle factors
        // is "squashed" into one step composed of the functions "block1", "block2" and "block3".
        // The expressions in the aforementioned functions are the result of explicit computations
        // combined with the Karatsuba trick for the multiplication of Complex numbers.

        let [v0, v4, v8, v12, v16, v20] = block1([ur0, ur4, ur8, ur12, ur16, ur20], MDS_FREQ_BLOCK_ONE);
        let [v1, v5, v9, v13, v17, v21] = block2([u1, u5, u9, u13, u17, u21], MDS_FREQ_BLOCK_TWO);
        let [v2, v6, v10, v14, v18, v22] = block3([u2, u6, u10, u14, u18, u22], MDS_FREQ_BLOCK_THREE);
        // The 4th block is not computed as it is similar to the 2nd one, up to complex conjugation,
        // and is, due to the use of the real FFT and iFFT, redundant.

        let [s0, s6, s12, s18] = ifft4_real_unreduced((v0, v1, v2));
        let [s1, s7, s13, s19] = ifft4_real_unreduced((v4, v5, v6));
        let [s2, s8, s14, s20] = ifft4_real_unreduced((v8, v9, v10));
        let [s3, s9, s15, s21] = ifft4_real_unreduced((v12, v13, v14));
        let [s4, s10, s16, s22] = ifft4_real_unreduced((v16, v17, v18));
        let [s5, s11, s17, s23] = ifft4_real_unreduced((v20, v21, v22));

        [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, 
            s16, s17, s18, s19, s20, s21, s22, s23]
    }

    #[inline(always)]
    fn block1(x: [i64; 6], y: [i64; 6]) -> [i64; 6] {
        let [x0, x1, x2, x3, x4, x5] = x;
        let [y0, y1, y2, y3, y4, y5] = y;
        let z0 = x0 * y0 + x1 * y5 + x2 * y4 + x3 * y3 + x4 * y2 + x5 * y1;
        let z1 = x0 * y1 + x1 * y0 + x2 * y5 + x3 * y4 + x4 * y3 + x5 * y2;
        let z2 = x0 * y2 + x1 * y1 + x2 * y0 + x3 * y5 + x4 * y4 + x5 * y3;
        let z3 = x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 + x4 * y5 + x5 * y4;
        let z4 = x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0 + x5 * y5;
        let z5 = x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0;
        
        [z0, z1, z2, z3, z4, z5]
    }

    #[inline(always)]
    fn block2(x: [(i64, i64); 6], y: [(i64, i64); 6]) -> [(i64, i64); 6] {
        let [(x0r, x0i), (x1r, x1i), (x2r, x2i), (x3r, x3i), (x4r, x4i), (x5r, x5i)] = x;
        let [(y0r, y0i), (y1r, y1i), (y2r, y2i), (y3r, y3i), (y4r, y4i), (y5r, y5i)] = y;
        let x0s = x0r + x0i;
        let x1s = x1r + x1i;
        let x2s = x2r + x2i;
        let x3s = x3r + x3i;
        let x4s = x4r + x4i;
        let x5s = x5r + x5i;
        let y0s = y0r + y0i;
        let y1s = y1r + y1i;
        let y2s = y2r + y2i;
        let y3s = y3r + y3i;
        let y4s = y4r + y4i;
        let y5s = y5r + y5i;

        // Compute x0​y0 ​− ix1​y3​ − ix2​y2 - ix3y1​ using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y0r, x0i * y0i);
        let m1 = (x1r * y5r, x1i * y5i);
        let m2 = (x2r * y4r, x2i * y4i);
        let m3 = (x3r * y3r, x3i * y3i);
        let m4 = (x4r * y2r, x4i * y2i);
        let m5 = (x5r * y1r, x5i * y1i);
        let z0r = (m0.0 - m0.1) + (x1s * y5s - m1.0 - m1.1) + (x2s * y4s - m2.0 - m2.1) + (x3s * y3s - m3.0 - m3.1) + (x4s * y2s - m4.0 - m4.1) + (x5s * y1s - m5.0 - m5.1);
        let z0i = (x0s * y0s - m0.0 - m0.1) + (-m1.0 + m1.1) + (-m2.0 + m2.1) + (-m3.0 + m3.1) + (-m4.0 + m4.1) + (-m5.0 + m5.1);
        let z0 = (z0r, z0i);

        // Compute x0​y1​ + x1​y0​ − ix2​y3 - ix3y2 using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y1r, x0i * y1i);
        let m1 = (x1r * y0r, x1i * y0i);
        let m2 = (x2r * y5r, x2i * y5i);
        let m3 = (x3r * y4r, x3i * y4i);
        let m4 = (x4r * y3r, x4i * y3i);
        let m5 = (x5r * y2r, x5i * y2i);
        let z1r = (m0.0 - m0.1) + (m1.0 - m1.1) + (x2s * y5s - m2.0 - m2.1) + (x3s * y4s - m3.0 - m3.1) + (x4s * y3s - m4.0 - m4.1) + (x5s * y2s - m5.0 - m5.1);
        let z1i = (x0s * y1s - m0.0 - m0.1) + (x1s * y0s - m1.0 - m1.1) + (-m2.0 + m2.1) + (-m3.0 + m3.1) + (-m4.0 + m4.1) + (-m5.0 + m5.1);
        let z1 = (z1r, z1i);

        // Compute x0​y2​ + x1​y1 ​+ x2​y0 - ix3y3​ using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y2r, x0i * y2i);
        let m1 = (x1r * y1r, x1i * y1i);
        let m2 = (x2r * y0r, x2i * y0i);
        let m3 = (x3r * y5r, x3i * y5i);
        let m4 = (x4r * y4r, x4i * y4i);
        let m5 = (x5r * y3r, x5i * y3i);
        let z2r = (m0.0 - m0.1) + (m1.0 - m1.1) + (m2.0 - m2.1) + (x3s * y5s - m3.0 - m3.1) + (x4s * y4s - m4.0 - m4.1) + (x5s * y3s - m5.0 - m5.1);
        let z2i = (x0s * y2s - m0.0 - m0.1) + (x1s * y1s - m1.0 - m1.1) + (x2s * y0s - m2.0 - m2.1) + (-m3.0 + m3.1) + (-m4.0 + m4.1) + (-m5.0 + m5.1);
        let z2 = (z2r, z2i);

        // Compute x0​y3​ + x1​y2 ​+ x2​y1 + x3y0​ using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y3r, x0i * y3i);
        let m1 = (x1r * y2r, x1i * y2i);
        let m2 = (x2r * y1r, x2i * y1i);
        let m3 = (x3r * y0r, x3i * y0i);
        let m4 = (x4r * y5r, x4i * y5i);
        let m5 = (x5r * y4r, x5i * y4i);
        let z3r = (m0.0 - m0.1) + (m1.0 - m1.1) + (m2.0 - m2.1) + (m3.0 - m3.1) + (x4s * y5s - m4.0 - m4.1) + (x5s * y4s - m5.0 - m5.1);
        let z3i = (x0s * y3s - m0.0 - m0.1) + (x1s * y2s - m1.0 - m1.1) + (x2s * y1s - m2.0 - m2.1) + (x3s * y0s - m3.0 - m3.1) + (-m4.0 + m4.1) + (-m5.0 + m5.1);
        let z3 = (z3r, z3i);

        // Compute x0​y4​ + x1​y3 ​+ x2​y2 + x3y1 + x4y0​ using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y4r, x0i * y4i);
        let m1 = (x1r * y3r, x1i * y3i);
        let m2 = (x2r * y2r, x2i * y2i);
        let m3 = (x3r * y1r, x3i * y1i);
        let m4 = (x4r * y0r, x4i * y0i);
        let m5 = (x5r * y5r, x5i * y5i);
        let z4r = (m0.0 - m0.1) + (m1.0 - m1.1) + (m2.0 - m2.1) + (m3.0 - m3.1) + (m4.0 - m4.1) + (x5s * y5s - m5.0 - m5.1);
        let z4i = (x0s * y4s - m0.0 - m0.1) + (x1s * y3s - m1.0 - m1.1) + (x2s * y2s - m2.0 - m2.1) + (x3s * y1s - m3.0 - m3.1) + (x4s * y0s - m4.0 - m4.1) + (-m5.0 + m5.1);
        let z4 = (z4r, z4i);

        // Compute x0​y5​ + x1​y4 ​+ x2​y3 + x3y2 + x4y1 + x5y0​ using Karatsuba for complex numbers multiplication
        let m0 = (x0r * y5r, x0i * y5i);
        let m1 = (x1r * y4r, x1i * y4i);
        let m2 = (x2r * y3r, x2i * y3i);
        let m3 = (x3r * y2r, x3i * y2i);
        let m4 = (x4r * y1r, x4i * y1i);
        let m5 = (x5r * y0r, x5i * y0i);
        let z5r = (m0.0 - m0.1) + (m1.0 - m1.1) + (m2.0 - m2.1) + (m3.0 - m3.1) + (m4.0 - m4.1) + (m5.0 - m5.1);
        let z5i = (x0s * y5s - m0.0 - m0.1) + (x1s * y4s - m1.0 - m1.1) + (x2s * y3s - m2.0 - m2.1) + (x3s * y2s - m3.0 - m3.1) + (x4s * y1s - m4.0 - m4.1) + (x5s * y0s - m5.0 - m5.1);
        let z5 = (z5r, z5i);
        
        [z0, z1, z2, z3, z4, z5]
    }

    #[inline(always)]
    fn block3(x: [i64; 6], y: [i64; 6]) -> [i64; 6] {
        let [x0, x1, x2, x3, x4, x5] = x;
        let [y0, y1, y2, y3, y4, y5] = y;
        let z0 = x0 * y0 - x1 * y5 - x2 * y4 - x3 * y3 - x4 * y2 - x5 * y1;
        let z1 = x0 * y1 + x1 * y0 - x2 * y5 - x3 * y4 - x4 * y3 - x5 * y2;
        let z2 = x0 * y2 + x1 * y1 + x2 * y0 - x3 * y5 - x4 * y4 - x5 * y3;
        let z3 = x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0 - x4 * y5 - x5 * y4;
        let z4 = x0 * y4 + x1 * y3 + x2 * y2 + x3 * y1 + x4 * y0 - x5 * y5;
        let z5 = x0 * y5 + x1 * y4 + x2 * y3 + x3 * y2 + x4 * y1 + x5 * y0;
        
        [z0, z1, z2, z3, z4, z5]
    }

    /// Real 2-FFT over u64 integers.
    #[inline(always)]
    fn fft2_real(x: [u64; 2]) -> [i64; 2] {
        [(x[0] as i64 + x[1] as i64), (x[0] as i64 - x[1] as i64)]
    }

    /// Real 2-iFFT over u64 integers.
    /// Division by two to complete the inverse FFT is expected to be performed ***outside*** of this function.
    #[inline(always)]
    fn ifft2_real_unreduced(y: [i64; 2]) -> [u64; 2] {
        [(y[0] + y[1]) as u64, (y[0] - y[1]) as u64]
    }

    /// Real 4-FFT over u64 integers.
    #[inline(always)]
    fn fft4_real(x: [u64; 4]) -> (i64, (i64, i64), i64) {
        let [z0, z2] = fft2_real([x[0], x[2]]);
        let [z1, z3] = fft2_real([x[1], x[3]]);
        let y0 = z0 + z1;
        let y1 = (z2, -z3);
        let y2 = z0 - z1;
        (y0, y1, y2)
    }

    /// Real 4-iFFT over u64 integers.
    /// Division by four to complete the inverse FFT is expected to be performed ***outside*** of this function.
    #[inline(always)]
    fn ifft4_real_unreduced(y: (i64, (i64, i64), i64)) -> [u64; 4] {
        let z0 = y.0 + y.2;
        let z1 = y.0 - y.2;
        let z2 = y.1 .0;
        let z3 = -y.1 .1;

        let [x0, x2] = ifft2_real_unreduced([z0, z2]);
        let [x1, x3] = ifft2_real_unreduced([z1, z3]);

        [x0, x1, x2, x3]
    }
}

#[cfg(test)]
mod tests {

    use rand::Rng;

    use crate::{implementations::monolith::{Monolith, state_generic_impl::concrete_u64_with_tmp_buffer}};
    use crate::field::mersenne::MersenneField;

    

    #[test]
    fn test_frequency_domain_24() {
        //cargo test --release test_frequency_domain_24 -- --nocapture 
        let mut rng = rand::thread_rng();
        let mut state = [0u32; 24];
        for s in state.iter_mut() {
            *s = MersenneField::from_u64_with_reduction(rng.gen::<u32>() as u64).0;
        }
        // let state = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0 ,0 ,0 ,0 ,0 ,0];
        // let state = [1, 1, 1, 0, 0, 0, 0, 0, 0, 4, 9 ,0 ,0 ,0 ,0 ,0, 0, 0, 0 ,0 ,0 ,0 ,0 ,0];
        // let state = [4, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

        println!("original state: {:?}", state);

        let mut state_u64_for_mul = state.map(|x| x as u64);
        let mut state_u64_for_freq = state.map(|x| x as u64);
        let rc = MersenneField::ROUND_CONSTANTS[0];


        let mut state_tmp = [0_u64; 24];
        concrete_u64_with_tmp_buffer::<MersenneField, {<MersenneField as Monolith<24>>::SPONGE_WIDTH}>(&mut state_u64_for_mul, &rc, &mut state_tmp);
        println!("state_u64_for_mul: {:?}", state_tmp);

        MersenneField::concrete_u64(&mut state_u64_for_freq, &rc);
        println!("state_u64_for_freq: {:?}", state_u64_for_freq);
        println!("states are equal: {:?}", state_tmp == state_u64_for_freq);

    }

}
