pub const RATE: usize = 8;
pub const CAPACITY: usize = 4;
pub const STATE_WIDTH: usize = RATE + CAPACITY;
pub const HALF_NUM_FULL_ROUNDS: usize = 4;
pub const NUM_FULL_ROUNDS_TOTAL: usize = 2 * HALF_NUM_FULL_ROUNDS;
pub const NUM_PARTIAL_ROUNDS: usize = 22;
pub const TOTAL_NUM_ROUNDS: usize = NUM_FULL_ROUNDS_TOTAL + NUM_PARTIAL_ROUNDS;

use crate::field::goldilocks::GoldilocksField;

// The Poseidon MDS and round constants are equal to those chosen in
// Plonky2 (https://github.com/mir-protocol/plonky2)
#[rustfmt::skip]
pub const ALL_ROUND_CONSTANTS: [u64; STATE_WIDTH * TOTAL_NUM_ROUNDS] = [
    0xb585f767417ee042, 0x7746a55f77c10331, 0xb2fb0d321d356f7a, 0x0f6760a486f1621f,
    0xe10d6666b36abcdf, 0x8cae14cb455cc50b, 0xd438539cf2cee334, 0xef781c7d4c1fd8b4,
    0xcdc4a23a0aca4b1f, 0x277fa208d07b52e3, 0xe17653a300493d38, 0xc54302f27c287dc1,
    0x8628782231d47d10, 0x59cd1a8a690b49f2, 0xc3b919ad9efec0b0, 0xa484c4c637641d97,
    0x308bbd23f191398b, 0x6e4a40c1bf713cf1, 0x9a2eedb7510414fb, 0xe360c6e111c2c63b,
    0xd5c771901d4d89aa, 0xc35eae076e7d6b2f, 0x849c2656d0a09cad, 0xc0572c8c5cf1df2b,
    0xe9fa634a883b8bf3, 0xf56f6d4900fb1fdd, 0xf7d713e872a72a1b, 0x8297132b6ba47612,
    0xad6805e12ee8af1c, 0xac51d9f6485c22b9, 0x502ad7dc3bd56bf8, 0x57a1550c3761c577,
    0x66bbd30e99d311da, 0x0da2abef5e948f87, 0xf0612750443f8e94, 0x28b8ec3afb937d8c,
    0x92a756e6be54ca18, 0x70e741ec304e925d, 0x019d5ee2b037c59f, 0x6f6f2ed7a30707d1,
    0x7cf416d01e8c169c, 0x61df517bb17617df, 0x85dc499b4c67dbaa, 0x4b959b48dad27b23,
    0xe8be3e5e0dd779a0, 0xf5c0bc1e525ed8e6, 0x40b12cbf263cf853, 0xa637093f13e2ea3c,
    0x3cc3f89232e3b0c8, 0x2e479dc16bfe86c0, 0x6f49de07d6d39469, 0x213ce7beecc232de,
    0x5b043134851fc00a, 0xa2de45784a861506, 0x7103aaf97bed8dd5, 0x5326fc0dbb88a147,
    0xa9ceb750364cb77a, 0x27f8ec88cc9e991f, 0xfceb4fda8c93fb83, 0xfac6ff13b45b260e,
    0x7131aa455813380b, 0x93510360d5d68119, 0xad535b24fb96e3db, 0x4627f5c6b7efc045,
    0x645cf794e4da78a9, 0x241c70ed1ac2877f, 0xacb8e076b009e825, 0x3737e9db6477bd9d,
    0xe7ea5e344cd688ed, 0x90dee4a009214640, 0xd1b1edf7c77e74af, 0x0b65481bab42158e,
    0x99ad1aab4b4fe3e7, 0x438a7c91f1a360cd, 0xb60de3bd159088bf, 0xc99cab6b47a3e3bb,
    0x69a5ed92d5677cef, 0x5e7b329c482a9396, 0x5fc0ac0829f893c9, 0x32db82924fb757ea,
    0x0ade699c5cf24145, 0x7cc5583b46d7b5bb, 0x85df9ed31bf8abcb, 0x6604df501ad4de64,
    0xeb84f60941611aec, 0xda60883523989bd4, 0x8f97fe40bf3470bf, 0xa93f485ce0ff2b32,
    0x6704e8eebc2afb4b, 0xcee3e9ac788ad755, 0x510d0e66062a270d, 0xf6323f48d74634a0,
    0x0b508cdf04990c90, 0xf241708a4ef7ddf9, 0x60e75c28bb368f82, 0xa6217d8c3f0f9989,
    0x7159cd30f5435b53, 0x839b4e8fe97ec79f, 0x0d3f3e5e885db625, 0x8f7d83be1daea54b,
    0x780f22441e8dbc04, 0xeb9158465aedacd3, 0xd19e120d826c1b6c, 0x016ee53a7f007110,
    0xcb5fd54ed22dd1ca, 0xacb84178c58de144, 0x9c22190c2c463227, 0x5d693c1bcc98406d,
    0xdcef0798235f321a, 0x3d639263f55e0b1e, 0xe273fd977edb8fda, 0x418f027049d10fe7,
    0x8c25fda3f253a284, 0x2cbaed4dc25a884e, 0x5f58e6aff78dc2af, 0x284650ac6fb9d206,
    0x635b337f1391c13c, 0x9f9a036f1ac6361f, 0xb93e260cff6747b4, 0xb0a7eae8c7272e33,
    0xd0762cbce7da0a9f, 0x34c6efb829c754d6, 0x40bf0ab6166855c1, 0xb6b570fccc46a242,
    0x5a27b90055549545, 0xb1a5b166048b306f, 0x8722e0ad24f1006d, 0x788ee3b3b315049a,
    0x14a726661e5b0351, 0x98b7672fe1c3f13e, 0xbb93ae77bdc3aa8f, 0x28fd3b04756fc222,
    0x30a46805a86d7109, 0x337dc00c7844a0e7, 0xd5eca245253c861b, 0x77626382990d8546,
    0xc1e434bf33c3ae7a, 0x0299351a54dbf35e, 0xb2d456e4fb620184, 0x3e9ed1fdc00265ea,
    0x2972a92bb672e8db, 0x20216dd789f333ec, 0xadffe8cf746494a1, 0x1c4dbb1c5889d420,
    0x15a16a8a8c9972f5, 0x388a128b98960e26, 0x2300e5d6ca3e5589, 0x2f63aa865c9ceb9f,
    0xf1c36ce8d894420f, 0x271811252953f84a, 0xe5840293d5466a8e, 0x4d9bbc3e24e5f20e,
    0xea35bc29cfa2794b, 0x18e21b4bf59e2d28, 0x1e3b9fc632ef6adb, 0x25d643627a05e678,
    0x5a3f1bb1ecb63263, 0xdb7f0238ca031e31, 0xb462065960bfc4c4, 0x49c24ae463c280f4,
    0xd793862c6f7b901a, 0xaadd1106bdce475e, 0xc43b6e0eed8ad58f, 0xe29024c1f2060cb7,
    0x5e50c2755efbe17a, 0x10383f20ac183625, 0x38e8ee9d8a8a435d, 0xdd511837bcc52452,
    0x7750059861a7da6a, 0x86ab99b518d1dbef, 0xb1204f608ccfe33b, 0xef61ac84d8dfca49,
    0x1bbcd90f1f4eff36, 0x0cd1dabd9be9850a, 0x11a3ae5bf354bb11, 0xf755bfef11bb5516,
    0xa3b832506e2f3adb, 0x516306f4b617e6ba, 0xddb4ac4a2aeead3a, 0x64bb6dec62af4430,
    0xf9cc95c29895a152, 0x08d37f75632771b9, 0xeec49b619cee6b56, 0xf143933b56b3711a,
    0xe4c5dd82b9f6570c, 0xe7ad775756eefdc4, 0x92c2318bc834ef78, 0x739c25f93007aa0a,
    0x5636caca1725f788, 0xdd8f909af47cd0b6, 0xc6401fe16bc24d4e, 0x8ad97b342e6b3a3c,
    0x0c49366bb7be8ce2, 0x0784d3d2f4b39fb5, 0x530fb67ec5d77a58, 0x41049229b8221f3b,
    0x139542347cb606a3, 0x9cb0bd5ee62e6438, 0x02e3f615c4d3054a, 0x985d4f4adefb64a0,
    0x775b9feb32053cde, 0x304265a64d6c1ba6, 0x593664c3be7acd42, 0x4f0a2e5fd2bd6718,
    0xdd611f10619bf1da, 0xd8185f9b3e74f9a4, 0xef87139d126ec3b3, 0x3ba71336dd67f99b,
    0x7d3a455d8d808091, 0x660d32e15cbdecc7, 0x297a863f5af2b9ff, 0x90e0a736e6b434df,
    0x549f80ce7a12182e, 0x0f73b29235fb5b84, 0x16bf1f74056e3a01, 0x6d1f5a593019a39f,
    0x02ff876fa73f6305, 0xc5cb72a2fb9a5bd7, 0x8470f39d674dfaa3, 0x25abb3f1e41aea30,
    0x23eb8cc9c32951c7, 0xd687ba56242ac4ea, 0xda8d9e915d2de6b7, 0xe3cbdc7d938d8f1e,
    0xb9a8c9b4001efad6, 0xc0d28a5c64f2285c, 0x45d7ac9b878575b8, 0xeeb76e39d8da283e,
    0x3d06c8bd2fc7daac, 0x9c9c9820c13589f5, 0x65700b51db40bae3, 0x911f451579044242,
    0x7ae6849ff1fee8cc, 0x3bb340ebba896ae5, 0xb46e9d8bb71f0b4b, 0x8dcf22f9e1bde2a3,
    0x77bdaeda8cc55427, 0xf19e400ababa0e12, 0xc368a34939eb5c7f, 0x9ef1cd612c03bc5e,
    0xe89cd8553b94bbd8, 0x5cd377dcb4550713, 0xa7b0fb78cd4c5665, 0x7684403ef76c7128,
    0x5fa3f06f79c4f483, 0x8df57ac159dbade6, 0x2db01efa321b2625, 0x54846de4cfd58cb6,
    0xba674538aa20f5cd, 0x541d4963699f9777, 0xe9096784dadaa548, 0xdfe8992458bf85ff,
    0xece5a71e74a35593, 0x5ff98fd5ff1d14fd, 0x83e89419524c06e1, 0x5922040b6ef03286,
    0xf97d750eab002858, 0x5080d4c2dba7b3ec, 0xa7de115ba038b508, 0x6a9242acb5f37ec0,
    0xf7856ef865619ed0, 0x2265fc930dbd7a89, 0x17dfc8e5022c723b, 0x9001a64248f2d676,
    0x90004c13b0b8b50e, 0xb932b7cfc63485b0, 0xa0b1df81fd4c2bc5, 0x8ef1dd26b594c383,
    0x0541a4f9d20ba562, 0x9e611061be0a3c5b, 0xb3767e80e1e1624a, 0x0098d57820a88c6b,
    0x31d191cd71e01691, 0x410fefafbf90a57a, 0xbdf8f2433633aea8, 0x9e8cd55b9cc11c28,
    0xde122bec4acb869f, 0x4d001fd5b0b03314, 0xca66370067416209, 0x2f2339d6399888c6,
    0x6d1a7918f7c98a13, 0xdf9a493995f688f3, 0xebc2151f4ded22ca, 0x03cc2ba8a2bab82f,
    0xd341d03844ad9a9b, 0x387cb5d273ab3f58, 0xbba2515f74a7a221, 0x7248fe7737f37d9c,
    0x4d61e56a7437f6b9, 0x262e963c9e54bef8, 0x59e89b097477d296, 0x055d5b52b9e47452,
    0x82b27eb36e430708, 0xd30094caf3080f94, 0xcf5cb38227c2a3be, 0xfeed4db701262c7c,
    0x41703f5391dd0154, 0x5eeea9412666f57b, 0x4cd1f1b196abdbc4, 0x4a20358594b3662b,
    0x1478d361e4b47c26, 0x6f02dc0801d2c79f, 0x296a202eeb03c4b6, 0x2afd6799aec20c38,
    0x7acfd96f3050383d, 0x6798ba0c380dfdd3, 0x34c6f57b3de02c88, 0x5736e1baf82eb8a0,
    0x20057d2a0e58b8de, 0x3dea5bd5eb6e1404, 0x16e50d89874a6a98, 0x29bff3eccbfba19a,
    0x475cd3207974793c, 0x18a42105cde34cfa, 0x023e7414b0618331, 0x151471081b52594b,
    0xe4a3dff23bdeb0f3, 0x01a8d1a588c232ef, 0x11b4c74ee221d621, 0xe587cc0dce129c8c,
    0x1ff7327025a65080, 0x594e29c44b8602b1, 0xf6f31db1f5a56fd3, 0xc02ac5e4c7258a5e,
    0xe70201e9c5dc598f, 0x6f90ff3b9b3560b2, 0x42747a7262faf016, 0xd1f507e496927d26,
    0x1c86d265fdd24cd9, 0x3996ce73f6b5266e, 0x8e7fba02d68a061e, 0xba0dec71548b7546,
    0x9e9cbd785b8d8f40, 0xdae86459f6b3828c, 0xdebe08541314f71d, 0xa49229d29501358f,
    0x7be5ba0010c4df7c, 0xa3c95eaf09ecc39c, 0x0230bca8f5d457cd, 0x4135c2bedc68cdf9,
    0x166fc0cc4d5b20cc, 0x3762b59aa3236e6e, 0xe8928a4ceed163d2, 0x2a440b51b71223d9,
    0x80cefd2bb5f48e46, 0xbb9879c738328b71, 0x6e7c8f1ab47cced0, 0x164bb2de257ffc0a,
    0xf3c12fe5b800ea30, 0x40b9e92309e8c7e1, 0x551f5b0fe3b8d017, 0x25032aa7d4fc7aba,
    0xaaed340795de0a0a, 0x8ffd96bc38c8ba0f, 0x70fc91eb8aa58833, 0x7f795e2a97566d73,
    0x4543d9df72c4831d, 0xf172d73e69f20739, 0xdfd1c4ff1eb3d868, 0xbc8dfb62d26376f7,
];

const fn align_round_constants(
    input: &[u64; STATE_WIDTH * TOTAL_NUM_ROUNDS],
) -> [[u64; STATE_WIDTH]; TOTAL_NUM_ROUNDS] {
    let result = *input;
    // this is obviously safe
    unsafe { std::mem::transmute(result) }
}

pub const ALL_ROUND_CONSTANTS_AS_FIELD_ELEMENTS: [GoldilocksField; STATE_WIDTH * TOTAL_NUM_ROUNDS] = const {
    // those are reduced, so we can just cast
    unsafe { std::mem::transmute(ALL_ROUND_CONSTANTS) }
};

pub const ROUND_CONSTANTS_ALIGNED_PER_ROUND: [[u64; STATE_WIDTH]; TOTAL_NUM_ROUNDS] =
    align_round_constants(&ALL_ROUND_CONSTANTS);

pub const ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS: [[GoldilocksField; STATE_WIDTH];
    TOTAL_NUM_ROUNDS] = const { unsafe { std::mem::transmute(ROUND_CONSTANTS_ALIGNED_PER_ROUND) } };
