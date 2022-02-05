use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use fff::{Field, PrimeField};

use crate::utils::{alloc, alloc_input, ZERO, ONE};

pub const WIDTH: usize = 5;
pub const R_F: usize = 8;
pub const R_P: usize = 60;

pub const ROUND_CONSTANTS: [[Fr; WIDTH]; R_F + R_P] = [
    [
        Fr::from_u256([0x881e25f47cacac6d, 0x6366869aac48f8d5, 0xdf7732861e09b0a9, 0x546f61d0cffb78fb]),
        Fr::from_u256([0xeb9c98dc512d20d2, 0xba62dfb4247528b2, 0x47028814745a9e4b, 0x2a3ebd6302072be2]),
        Fr::from_u256([0xe8e09c75ee9c1cf7, 0x71845dfe9599c4af, 0x1de7b9bcc9c0ffc6, 0x37a0f54ae3995b0c]),
        Fr::from_u256([0x8c81b0f828640b2f, 0x683fa964b7bc0a82, 0x872f6b47c07ddd8b, 0x1d8080d1ff88cc92]),
        Fr::from_u256([0xe5c5e52b4bdd93ab, 0xa044d16b200c2630, 0x4ee2721249b99967, 0x06d9fbe66a04bb1c]),
    ],
    [
        Fr::from_u256([0xe9a1400bc3707153, 0x4877d2d8b5990e4d, 0x79f4185000d8e6bd, 0x092fc88676eb19b2]),
        Fr::from_u256([0xcde84d71ecd086ca, 0x186501f63759949e, 0x1f27cd5ee94c7777, 0x6f0f1c22fe4e4016]),
        Fr::from_u256([0xc4e6368fb78ae770, 0x8cb79b21ee145789, 0xe3cb4a24130a1221, 0x05e81407804ff710]),
        Fr::from_u256([0xa7f450d2deefadc8, 0xac3e53e2b9f78bb8, 0x3f77d90fb33772dc, 0x17f8cdea6b6730c5]),
        Fr::from_u256([0xb0edba93198ea39b, 0x3c1badecd8c7cc9c, 0x3ba9a044bfe188a7, 0x32cf5a5dd4246aa3]),
    ],
    [
        Fr::from_u256([0x1b153b537ca524b4, 0xb7564ae8d6c0fd7e, 0x87cd7aabe2c0c142, 0x2641255acacb05da]),
        Fr::from_u256([0xc2d76c2c6f6b11d6, 0x3056ad0e6019fdd5, 0x66cef80fb4bceac0, 0x6cae98d7de6aab50]),
        Fr::from_u256([0xd2af3a4792a36208, 0x343be1d024b0ce68, 0x509d480082f9b39b, 0x6508c5bde232dc4d]),
        Fr::from_u256([0x3e8a6d21093ead58, 0x7fb8596a1f4c32bf, 0xf0be82a543036470, 0x55cecdd3416da543]),
        Fr::from_u256([0xa4ce9ca08929edad, 0x2124c419c00ca937, 0xdd847d0bff70898e, 0x45e939a14965ac0b]),
    ],
    [
        Fr::from_u256([0x34d21e028c14fb79, 0xafb34449f2c0fac0, 0xd0a1e6a85e649117, 0x052aaf3519e0d0de]),
        Fr::from_u256([0x336bc7a69df78df7, 0x85eefa07dcc4a7c7, 0x0fbed55dd3e42889, 0x73c6bd21ba92212f]),
        Fr::from_u256([0x13864b096883cbdd, 0x5eb50e64d418258f, 0x26312707bce811db, 0x5ec3f4485a9338ae]),
        Fr::from_u256([0x5d056cd68ba2a222, 0xfc0d8660a6896474, 0xf0605c72d096a783, 0x3151a427e6a950be]),
        Fr::from_u256([0x87b16ec41558b3e3, 0x796f9ad5882390fe, 0x438af49349c01791, 0x68e7c8e58f277958]),
    ],
    [
        Fr::from_u256([0x07422e9c8c313b6c, 0x0f7617745120c423, 0x7dfb0408ac05b8ae, 0x089b1336215987e0]),
        Fr::from_u256([0x7aa86dc4a75c0c82, 0xc9ea717838108fe5, 0xd4bedcdf6f1a83b5, 0x19abd80ba112c189]),
        Fr::from_u256([0x4227f1860ffbbf99, 0x4153226063c75f4a, 0xebd85a3399433e08, 0x2d0da3681aad1d6f]),
        Fr::from_u256([0xeab9d5643d5db9af, 0x3fdfb9061b453666, 0x4329c292f4c95a4f, 0x2dd98474fd4e2160]),
        Fr::from_u256([0x08f8bfe7d166f285, 0x9c478f2574f4eb36, 0x711b22fa2023aacf, 0x28d54a2718d9b64f]),
    ],
    [
        Fr::from_u256([0x1f5d2e3d6c9d7f6e, 0xb4b607a6f6ede611, 0xf65551c8246ba359, 0x0e24ba2a75e89ae5]),
        Fr::from_u256([0x7d12bda6d8159962, 0x3c6cfc85de72a869, 0x8ba9e18582ebd97e, 0x17a9bf2cf5b0cbe3]),
        Fr::from_u256([0x1b1b5c297a7b3d5b, 0x231bfe3077e509ff, 0x39895954c56e4fa1, 0x6fff72223282ff51]),
        Fr::from_u256([0x8c02476268043512, 0x42e12e8b3a716e2f, 0x3e6dee044c1cef13, 0x30debcbb3b41caf1]),
        Fr::from_u256([0x8ab85e25f1fa33eb, 0xf7db786a19cbbb49, 0x2dac799d9a34483a, 0x4121f62e66806ab9]),
    ],
    [
        Fr::from_u256([0xcd3e121a70fc840e, 0xfca6ef9326263964, 0xc83a2a13a26d95e4, 0x2a5ab9c9eb2a9380]),
        Fr::from_u256([0xced90d53bd3c8a0f, 0x1381d483e9536385, 0x280a27797964e4f7, 0x6e351626aba62892]),
        Fr::from_u256([0xe7fa89bb5f30fb9f, 0x1bc05e4ff7fc06cb, 0xa20eea367676a3ea, 0x640d607931cc1855]),
        Fr::from_u256([0x880a0855647917b3, 0x66e2e00d463379df, 0xf8020c4d8d64c6f6, 0x6f649eee02a799e2]),
        Fr::from_u256([0x22ed3b1322db5d4e, 0x5a8b3e75dec7e35d, 0x8e63ee840aedfad3, 0x6035fa9afe88cc78]),
    ],
    [
        Fr::from_u256([0xd4db0631ea886568, 0x8f7e0f676450cd53, 0xd032178bc0497da2, 0x47b20ede94dcdb25]),
        Fr::from_u256([0x1ce8aa83c1fc82e4, 0x7b1a02bcd11df8c7, 0x0af477c73f397f95, 0x3c661e16b607a70a]),
        Fr::from_u256([0x9891ccfcc9d7c4f7, 0xdbe7f5a5f91d930c, 0xd52a25b32a80d3ad, 0x58ddb6c6bbcb34a6]),
        Fr::from_u256([0x493abfaed2241c44, 0x7333bd930bd6bb91, 0x28223889461fcbe8, 0x5d10dcb77ed7e7ce]),
        Fr::from_u256([0x9a73723757b49a70, 0x173ee41d735dbcf2, 0xf097fab42e8919ef, 0x5d0b1aad9ae1108e]),
    ],
    [
        Fr::from_u256([0xb947fad96e60152c, 0xeeb2db918a77cae8, 0xbd6ddbea95fc9e05, 0x6fe504c2805a6278]),
        Fr::from_u256([0x88373298d9e065cf, 0x71990ba4fb431aa6, 0x6ab2bb30c926f82f, 0x18ea1dde128bf22e]),
        Fr::from_u256([0xe9cf42c95e781ae6, 0x15624d17945a773c, 0xea4ea7e0debf0976, 0x05c4815afe66bf06]),
        Fr::from_u256([0xc2fb00fe0ee1d75a, 0x1281ca4563c3835a, 0x17a623926f511a6a, 0x32fba106f88052ce]),
        Fr::from_u256([0x03d1cf188626fc73, 0x5983631145e2dd37, 0xda699d224351c28b, 0x50511c685a39b172]),
    ],
    [
        Fr::from_u256([0xd7c0d5aec1301e0a, 0x1596c8c6833d1453, 0xb0a55bc434cee2e5, 0x2bf3f8aa91c9aa58]),
        Fr::from_u256([0x519a808cfdb832e7, 0xf78a7e0248d100ec, 0x9f6e6a59a0402e3a, 0x248132108b172a0d]),
        Fr::from_u256([0xa2820b473eac5506, 0x8f370cc3537d8d71, 0x161173d607b47c11, 0x6cdaabbed38acdef]),
        Fr::from_u256([0xd5dd856bd3d44455, 0x1aeed61fc476c053, 0xf8d0360004336477, 0x3a860d63ba043c90]),
        Fr::from_u256([0x6cc560b20835ed26, 0x4efaf79e93f5ed42, 0xee28b42acf5bce31, 0x247e88c37b0c30fa]),
    ],
    [
        Fr::from_u256([0xb5d3148fdff08c89, 0xfb08e3a234ca65f9, 0x37e3e08d5dbd4eb7, 0x67077ed5ed71bcbb]),
        Fr::from_u256([0x8f944c8938d9596f, 0x63a7177fe016a323, 0x4d4e07a47d228058, 0x4d31e29bf8b50674]),
        Fr::from_u256([0x61517522845e13f0, 0xe21b53e67fb83f91, 0x32711b8009408f2f, 0x0e5c434fe7cd7296]),
        Fr::from_u256([0xe53b562121572b97, 0x4ff16738f9bfc2ca, 0x6335b416b24ad1e2, 0x3b5eec822a7369a7]),
        Fr::from_u256([0x002c48818da04f58, 0x6fced291b47905bd, 0x6675eb71a0dc5973, 0x656b27d6d568dc3d]),
    ],
    [
        Fr::from_u256([0xa3e575121c4a1851, 0xaae481fb0b63caa9, 0xcc6a5a9fd8c023b8, 0x452efa67b8f0283f]),
        Fr::from_u256([0x8412991edd6b73a6, 0x4cc60697a324ae71, 0xb84c46a809ccdb24, 0x21713c18be252a51]),
        Fr::from_u256([0xb6eb39f7f9fa8302, 0xa9864969d7f5cd34, 0x764f5777d64ab1dc, 0x247d423d20fd8b0f]),
        Fr::from_u256([0x7883125717108821, 0xb29d815b1d54540d, 0x25d9b913dee3eb9d, 0x71812ba40a4aadc2]),
        Fr::from_u256([0xef58340d7d4eea9c, 0x7ad14942d8e13871, 0xaa92c7aca6a37f9d, 0x0c0418d2fb065b6d]),
    ],
    [
        Fr::from_u256([0xddc25dac377d29c6, 0xc2ad29cbe990612f, 0x551665cdb650d1d8, 0x5775088f1e9f1060]),
        Fr::from_u256([0x0a0b3aaf57500e50, 0xe9a7d853733cd712, 0x351ecc02cde964a9, 0x1127aca13248dffc]),
        Fr::from_u256([0xd460208b5db1f836, 0xd08b414e3ebf7869, 0x6a53927de7c2922d, 0x1dd87167aafaf102]),
        Fr::from_u256([0xe2bfe4a3345ace4a, 0x02d50f3ac2270cc9, 0x278d59a982c20d69, 0x098117600dce1170]),
        Fr::from_u256([0x71f880183d7ac12d, 0x0259ca1bcb25dc8a, 0x3de4e14ea9b86f15, 0x5d17a818e18e9aa4]),
    ],
    [
        Fr::from_u256([0x174e00d4281b56e3, 0x70686b6d1e5b1160, 0x6c2982da582a625c, 0x48491efceb4d77fb]),
        Fr::from_u256([0x3647276a1ed820a5, 0x68efa9eea15b5b63, 0x46d86ba93867ef52, 0x1160bc7e5ccc22e2]),
        Fr::from_u256([0xde9aba9e6cab93c7, 0x1053bbec4bb1b730, 0x8f3ae9c33369847a, 0x2c2dddc2ef32fe5a]),
        Fr::from_u256([0x4dce3ca9ed16fefc, 0xe23582fab93a7593, 0x4ca1ad0e9cda0713, 0x32a98126f3e9878e]),
        Fr::from_u256([0xc6943ae934a8b33b, 0x81020bcd1c236b7e, 0x03e53f02704b475a, 0x6102022f3f34719b]),
    ],
    [
        Fr::from_u256([0x19306786e6d900ea, 0xce3a00f367ad63d0, 0xe73f1181882e0557, 0x2c59fc6293649713]),
        Fr::from_u256([0xd695e76355acd2b5, 0xbc9916693dd898b2, 0x9fac50991d7b2cd4, 0x34461c7d27aaa7b9]),
        Fr::from_u256([0x81c8984b076d7634, 0x3fbc2020188839e8, 0x58176d13d0943301, 0x590f0a9b8e79d02d]),
        Fr::from_u256([0xfdec923c8c91793d, 0x84b08b29ccca1af8, 0x2ff5679b48fc8223, 0x259088335e1f9931]),
        Fr::from_u256([0xe78f954c81c5b63e, 0xfb5358bf0448741d, 0x9f8ee6739d5e7347, 0x4cb841a45e515492]),
    ],
    [
        Fr::from_u256([0xe2bcd9f726cabf0b, 0x691285029e7cbe19, 0x1e9b58a1955b033d, 0x29739a3212127dc1]),
        Fr::from_u256([0x78ef218ccd2372dd, 0x5d7b1bb905efdaa5, 0xbaa8b75c118d277c, 0x7251f8a9e10ceca6]),
        Fr::from_u256([0x69faab818a94eddb, 0xdb3be255ffa96b96, 0xe45e76ce2a9420ff, 0x60367a485625fb67]),
        Fr::from_u256([0x86d8e904c3c1dab3, 0xb001d53a28146a1f, 0x5802e68c45d530aa, 0x259f70997eec5da1]),
        Fr::from_u256([0x31469fbcadf93115, 0xacd9cdecff39e431, 0x7b20b8f8a1c76cd2, 0x4f677e6cb44ab589]),
    ],
    [
        Fr::from_u256([0x79956211bd502d75, 0x64e1da1e7d737486, 0x81d6e60b298dd312, 0x3fe4e9a17ab212d8]),
        Fr::from_u256([0xb2a78434ad1704fd, 0x26f5e1adfe24fcf7, 0x6c4be02a5cde4639, 0x2c21a3ef65bfc220]),
        Fr::from_u256([0x584c1534e60ab31b, 0x91f7171812f91d61, 0xb91f830c7c851d7c, 0x38b0c1ee7fbea5d3]),
        Fr::from_u256([0x9ea61187def237bd, 0x65611bb3621be2dd, 0xdfcf624677348451, 0x1b241682bb0165c6]),
        Fr::from_u256([0x4dcf8dc98030c75d, 0x7fc11ed9e459c87e, 0x910a19212a19b63b, 0x1f54c83a023ad243]),
    ],
    [
        Fr::from_u256([0x61591c678150cdd2, 0x3f2a6724e4c72741, 0x81e67a7ce5f35a01, 0x44260eb60bf528b5]),
        Fr::from_u256([0x728ce73d34d89fbc, 0x9bea4142df159d9c, 0x1063f566005771b8, 0x69a52d251ee4b224]),
        Fr::from_u256([0xd4f0fb51b84924f3, 0xc67bfa579c2c31cd, 0x99ce8ae894d539c2, 0x5ce4515f40144fab]),
        Fr::from_u256([0xd377a90f90f20c73, 0x3265d584c4cab9bb, 0x889d95c8f8addfaf, 0x0339b15f4d52f7b6]),
        Fr::from_u256([0x151235b0dadea957, 0xdde2092075bee10f, 0x04d07924afebbb45, 0x723647b6cc8a9008]),
    ],
    [
        Fr::from_u256([0xd693744e779d5f83, 0xcf6e55ad9805dd4b, 0x1f0262300852addc, 0x2f00f7fab1874be0]),
        Fr::from_u256([0x697cce78017c184e, 0x72743ce35f65aa26, 0xb64ff22b67c8b967, 0x36ec90dca13d00ed]),
        Fr::from_u256([0x7d745ec12bfedbd3, 0xd7e5573d50754775, 0xb2122c9c4d7e00da, 0x3952ab14a53b5b9a]),
        Fr::from_u256([0xd64acaaa1012e569, 0x75e4a2d25965f6cc, 0xcba90789eab90d10, 0x0956f2098d789ac6]),
        Fr::from_u256([0x59d93a78c1a4dcab, 0xedaae1f3e68ea15f, 0xcb8800d6f84026fa, 0x51e2980e8a29e2e5]),
    ],
    [
        Fr::from_u256([0xe47b94f4a591f322, 0xc4e4ccf950f626f0, 0x4f19c490b0a7f2eb, 0x682db6ca1356bd45]),
        Fr::from_u256([0x8bbd8c4d1a09b769, 0x098fa1ddb32c9d39, 0xe5f3758eabadf38b, 0x6e82a0b5b851c29d]),
        Fr::from_u256([0xe602081d13b4f730, 0xdd76fb2917182d04, 0xedb45185deadb7dd, 0x1c832672517cb257]),
        Fr::from_u256([0x139bcbc64ca67ff6, 0x14b4739495644dc5, 0x66bd95610a084a5d, 0x6afdbd3951b427bc]),
        Fr::from_u256([0x5f8fb1997811d0cb, 0x658b445be0fe7161, 0x4fbd74dc6f18f026, 0x353633a8a1832819]),
    ],
    [
        Fr::from_u256([0xfe51b836b3fdb167, 0xcb2258bf73f1a366, 0x5775a7f45f1847cb, 0x448c09988a75e228]),
        Fr::from_u256([0x5581376c58930304, 0x3a1b6c20a7bea56b, 0xe3ebb526ebffe004, 0x6a661c2b23562bbc]),
        Fr::from_u256([0xb5eeab1a07cb5237, 0x87ea465192ecedac, 0xb8a6d8fb491ff3fb, 0x4762355ebc2c514f]),
        Fr::from_u256([0x183dda317bc59086, 0xf1777096105beea1, 0x42f6e7430c87ca09, 0x1aa193535651b0ff]),
        Fr::from_u256([0x4cbd9f1e505c8b90, 0x79e337db7eb62e8c, 0x9ac35bf3fa3ab89b, 0x25f02e6f97fcf9ca]),
    ],
    [
        Fr::from_u256([0xc20dc518929d1d99, 0x89a45aabde4686fc, 0x086cd11cec72c581, 0x6afe72006a258bdf]),
        Fr::from_u256([0x8b92b6982d7ca379, 0x52dbde76dc829c18, 0xca33844e1f0c921f, 0x39db6e31dd895610]),
        Fr::from_u256([0x08efea9a47e30237, 0xc3b0ac101c16378f, 0xa505471ea2b647e0, 0x674cd3759df33603]),
        Fr::from_u256([0x25b90cd3b6d5700d, 0x2cf48ea560c676ab, 0x55e7d68c3cf75cda, 0x0bda28a210650855]),
        Fr::from_u256([0x39dba6f113d87062, 0x9a69f4f4629392b7, 0xd6a52dd3f8725416, 0x2efbdb072ba7fac0]),
    ],
    [
        Fr::from_u256([0x84e508e249ac0a92, 0x114f41af339de8cc, 0x04384ec78d48abe2, 0x158955c521d1c600]),
        Fr::from_u256([0x2ebda779878735a4, 0x71b99c6fb2319789, 0x2c28d7357c3c7a7a, 0x6be6a86033dfbd49]),
        Fr::from_u256([0x7d8c2d337b3a5712, 0xf20c9ffd07dd7c32, 0xae3ad3424d683eee, 0x37fe83f69888345b]),
        Fr::from_u256([0x5d84d567870cf2a0, 0x35e3858c92830dd2, 0xcffa838554d3fea4, 0x68c5d89feffbcf54]),
        Fr::from_u256([0xf999d36dc0a5d5b9, 0xabc54715bce2ea00, 0x2eabba21331c19ad, 0x22194492fd0a7b91]),
    ],
    [
        Fr::from_u256([0xec7810d10ca2e91e, 0xd775a00b39a7ec54, 0xbfd7ba795eb4dacc, 0x07640d1d2a94e97f]),
        Fr::from_u256([0x49d918db3ee204f2, 0x357cc8edfcae3f37, 0xce9fbbdd672ad098, 0x277df81c29e197db]),
        Fr::from_u256([0xd61c863531258422, 0x770f570f14469a10, 0x54815331bc8bec0d, 0x49a296e57c8039fd]),
        Fr::from_u256([0x923168103d1beebf, 0x756546f4b3081409, 0x09e2831b80e0f18c, 0x0b9674d2a468d4b5]),
        Fr::from_u256([0x56e6a09b4d93e10b, 0xf7c9587cbd480642, 0x0fcd77ba345f3152, 0x5b8e2284a837d514]),
    ],
    [
        Fr::from_u256([0x12684ec0860438d3, 0x15c57379295f66e2, 0x9297f97a9c71f42e, 0x1843625311138343]),
        Fr::from_u256([0x9430bf5aa95915c5, 0x0269f856cf810cc5, 0x53cdca369a2d111e, 0x049bbe75b18918b6]),
        Fr::from_u256([0xa6a0b829c585e7b2, 0x934b370e088fb658, 0x6b7b75650220fced, 0x51f89a65896da70b]),
        Fr::from_u256([0x41017f2d6b0a4e53, 0xf44f7f7d53d4eb7c, 0xc5cd0cee54ebb700, 0x4818ba569c3380de]),
        Fr::from_u256([0x2a09570bf196939b, 0x45cb0134aaaeb277, 0xc71aabc9dd4bd8a4, 0x168012c566d63eff]),
    ],
    [
        Fr::from_u256([0x7680027f88af75eb, 0xc505ca1968599262, 0x7edacac6857551e6, 0x12f9b8835d6f6117]),
        Fr::from_u256([0xd119e12e30a9ba69, 0x8d4e06c6793c7b45, 0x4fe3494a6a19c684, 0x593bdd59c2e69d89]),
        Fr::from_u256([0x0dcea49bb83027ad, 0x78bc684f3cd558ad, 0xa64984b3c91f1c8e, 0x372bc48f2bf37872]),
        Fr::from_u256([0xc01dcadded5956ce, 0x90ac2cf98ab356d9, 0xb5bb2877ae1f31dc, 0x1e27bf0a9cd3a381]),
        Fr::from_u256([0x1125e665bfc42793, 0xe628315756162987, 0xed7ffc2cf18e3e09, 0x0eed6514885f16ee]),
    ],
    [
        Fr::from_u256([0x7e334850057003a3, 0xbdd74727c072fc08, 0x1c9e0c8b8fbdfde2, 0x64b00cce34389172]),
        Fr::from_u256([0x52d69c0616e3064d, 0x8becd86a1ba75dea, 0x3c7fad63e209e764, 0x450e7303082a2d32]),
        Fr::from_u256([0x003a9f073ae4ec2d, 0xbbb09ad96defd21c, 0xe9b08cb4ae1b6608, 0x2997a2f5b762936a]),
        Fr::from_u256([0x9386d76941eabf33, 0xabcd8f29ff7e31d8, 0xb364d1ad3167f901, 0x350b68024f4e28e9]),
        Fr::from_u256([0xb04a6840f77d8551, 0x07a0920d114bdcb4, 0xb3e0127d52532683, 0x6356d73a842e2dd2]),
    ],
    [
        Fr::from_u256([0xce3732a3957a3b0a, 0xb83b8f261e3fe59d, 0x31e99b0be0ab2573, 0x528b90dabedabb77]),
        Fr::from_u256([0x040ef7b7dc8eb8de, 0xa13993b2ff68a8d4, 0x978e9bd3755e0654, 0x2d12034930181ffe]),
        Fr::from_u256([0xde42a46888e0432b, 0xc85f1449338e3c9b, 0xf86ebabfe6290a46, 0x6030bcd75f02f649]),
        Fr::from_u256([0x31f8e3cda3f3dfc9, 0x9ca398002af46a9c, 0x85fc13385b8a296b, 0x4b535c7d79772873]),
        Fr::from_u256([0x78460f2adba0d4b5, 0xb9c7ccb63b6b312a, 0x7874f1d9491c65c1, 0x50f19b08a7785ffa]),
    ],
    [
        Fr::from_u256([0xa378666976c57dff, 0x7b21e689e826ed65, 0x559af7b044e0c40a, 0x0b152a9fdac358cb]),
        Fr::from_u256([0x6f5b62274bf73133, 0x016f752a61ddd430, 0x3e5905074729d4f3, 0x1dbf02d15b5d50fa]),
        Fr::from_u256([0xac465a2800e04af6, 0x7a1ad02b1793c322, 0x934b7c11ee83512e, 0x3d6d40fad4947064]),
        Fr::from_u256([0xcf6be6fce6efa689, 0x9b0f20d2df722c3b, 0x90240d2f3004f61b, 0x6c477fb88708cfd6]),
        Fr::from_u256([0xcb00e45ea8419d9c, 0xa3d301c44b66dab0, 0xc179e555494dbd61, 0x2cc34873a9097a51]),
    ],
    [
        Fr::from_u256([0x971395ca812c3f2b, 0xa2f122c31f42e549, 0xd2749ee2fda9b3f5, 0x3b78ee11ce9560bb]),
        Fr::from_u256([0xbc3ff429833aaaf8, 0x4c4ad8cbe9b6deaa, 0xed655e911f8ee51f, 0x63c6f3221b3ba081]),
        Fr::from_u256([0x78a86866306238d8, 0x12211f3509098d4e, 0x9c3e7cd24f7c5112, 0x42576a0c194ccfa5]),
        Fr::from_u256([0x016506eeb1a5d3a3, 0x50f6778c806f6f47, 0x73b139badfb52858, 0x446d85eb34bd614f]),
        Fr::from_u256([0xcf685aa13d546beb, 0x4f353a8772713d29, 0x866b9c0ade960a2d, 0x3d2b31f0175b360b]),
    ],
    [
        Fr::from_u256([0x463dfd13c89c7c21, 0xd3b805979a968e2e, 0xf4ee6da672bce226, 0x2b1e8a55beacd979]),
        Fr::from_u256([0x7c3d541a45b20859, 0x6ae045f546f24d1d, 0x77cf76c63a5de72b, 0x0b9ee05e50f89e91]),
        Fr::from_u256([0x35a9da38604f098c, 0x50bc37692ca1bf4b, 0x873e9ebe96888594, 0x3f632e3f9d09a6fd]),
        Fr::from_u256([0xdfbfaa3c21be3988, 0x03e6790649732896, 0xd7ba4f2224613526, 0x43c04525418d4344]),
        Fr::from_u256([0xde819352ed3ca4c4, 0x6b780c884d90b65b, 0x3096fef7ee82a524, 0x4c934a3474f126e5]),
    ],
    [
        Fr::from_u256([0x96523ecfa53ed58e, 0xe269073ee85c419f, 0xc7d59577969ed19c, 0x2c8eaecaed354228]),
        Fr::from_u256([0xedb8bb1becab8d65, 0xbf063847274415fc, 0xc6a27a14e5c28a50, 0x650003e7e7822e78]),
        Fr::from_u256([0xbd06b5a1bb712750, 0xc6af1086c0f79800, 0x3a6aae8ee503b13a, 0x55f3c65f9ec4a864]),
        Fr::from_u256([0x47c5ec20b6edc9d7, 0x412b2953efa1869c, 0xa6898d7137a54e6d, 0x12e56ab98756fa38]),
        Fr::from_u256([0xa6a3f145e3f8a8f1, 0x3b5c4a18d2c41bd1, 0x4d8a47321fa08076, 0x07d4b95e16b746e3]),
    ],
    [
        Fr::from_u256([0xa1f80d7e050d8045, 0xc080ef9f2647a9b4, 0xc6ffcb0e7833fbc4, 0x4316a60aafe5ce18]),
        Fr::from_u256([0x3c7a64507cfa7568, 0x721fea101b5bea67, 0xb6f35d2256d2a28b, 0x231d21b1216da10b]),
        Fr::from_u256([0x07ae7e86ab9462ca, 0x5ed14303d861868c, 0x5afb5577e6d5c900, 0x2907de9117b1f898]),
        Fr::from_u256([0x58f9af64aeed9b1e, 0x771a0cf85c94d8e8, 0x69bec25f15745909, 0x45b6540b7471e01c]),
        Fr::from_u256([0xadcb14519c300ce1, 0x6203c42cd8655ec3, 0x79bf6175bb590431, 0x4bfad783f9104ed7]),
    ],
    [
        Fr::from_u256([0x28a7166510c505f9, 0xd072512817ab7148, 0xa89c50ad4ce71eb0, 0x327e14ccd4be9ffc]),
        Fr::from_u256([0xba4febf81c82801f, 0x56c79047f48980fb, 0xa449b407dc335578, 0x6afcd3f7ba166f5b]),
        Fr::from_u256([0xa86d016f8773d154, 0xd064de46e1ea11a5, 0x4a6432bbaf5c95a5, 0x5e3f63d9d7e9467e]),
        Fr::from_u256([0x474f27eddd749d3a, 0xb20814959ba6e641, 0x70c19e8df7e9a018, 0x6cb3878ffbdc988f]),
        Fr::from_u256([0x015c27614aa50396, 0x14032a1925bbc10a, 0x86f9d26eaf458f80, 0x197de27efa38588a]),
    ],
    [
        Fr::from_u256([0x5e58711fbeb6f976, 0x02395d70ddea420c, 0x82f863e25116394e, 0x5c05eb66daae20f5]),
        Fr::from_u256([0xa87e4c02ce4cf75f, 0x94561962388410c4, 0x4e6ff61b37cda61d, 0x73428166eb462342]),
        Fr::from_u256([0x457b028006b06049, 0xc545133695a9cc4d, 0x62dfbb405157ee61, 0x4bcdbdd32eeeb7d8]),
        Fr::from_u256([0x8964c441f871bf4b, 0x25b91360655a8294, 0xe566119c9c91e2eb, 0x306999dc6fb9bb19]),
        Fr::from_u256([0x3459af8d7d42081f, 0xb76e2f4ed0798d36, 0x9865a23e23621972, 0x38eac918aff0502e]),
    ],
    [
        Fr::from_u256([0x78f5abc902409c29, 0x2de744c748f0f12e, 0x27376613214ed5c4, 0x46f4ec0faa0f9f93]),
        Fr::from_u256([0x3ceb6b209abe03d7, 0x477ae4b070ae905c, 0xacf4e8d0e360a995, 0x4a33fa2a5354bdb2]),
        Fr::from_u256([0xc8db78d8f158d6e6, 0x2675fb81e73bfc49, 0x34e35bc73835df7c, 0x4f70513514b6a1dc]),
        Fr::from_u256([0xa34c40a5b9b1b7de, 0xb08dc8a018843c33, 0xb3d3347c94184e67, 0x0061504a5008ee1f]),
        Fr::from_u256([0x644ed6a71df55fed, 0x0998d531992b1218, 0xbe7f7a9b4c9cfeb3, 0x541c54b030000862]),
    ],
    [
        Fr::from_u256([0x5f5cfd8abc0b6390, 0xd28aebdbd4809c6d, 0xc5de524b2ec05239, 0x483d8519d2964d2f]),
        Fr::from_u256([0x53625a38916fbc05, 0x08dad254912aaf59, 0xce657938af20075e, 0x277d9ee29f5c2b01]),
        Fr::from_u256([0xd80908c3d1cea721, 0xbbc167bc4f4bad1d, 0x4cbcbff2816b9ca0, 0x42a71a953db150b3]),
        Fr::from_u256([0x9d8ff0c6e87448c6, 0x42acb067ff35874c, 0x06321b06d72a2a76, 0x24418d4de746c0dd]),
        Fr::from_u256([0x8ec046ebd1264c3a, 0xdadb77c01d64869a, 0xad6b639364c1056c, 0x4a539a8b1cbd4f50]),
    ],
    [
        Fr::from_u256([0x1e84c391387170ca, 0xf309e51f13764147, 0xdd296ff06e44a011, 0x70b0a9f7eab1201c]),
        Fr::from_u256([0x9e964eefea49568e, 0xd84045aef7dea6f8, 0x6922c38aa6e2599c, 0x4b9440640863dc13]),
        Fr::from_u256([0x0d5a24435981c6ac, 0x99d03711e57c31c3, 0x80232f2502ab974e, 0x06ab331f665e159c]),
        Fr::from_u256([0xf13648a23488b0b8, 0xfaeaceed5ee40f12, 0x003789cdf097e84a, 0x4ff2bf5903c67978]),
        Fr::from_u256([0x90b17e3276355417, 0x2e286edb7b286d2b, 0x6a0ba43e03264e61, 0x496cc0bb85d282f0]),
    ],
    [
        Fr::from_u256([0xe2f3a2eaf4f02e1d, 0xe07bcaca826e79fa, 0xee329ceb5f943a61, 0x267892b0ce089601]),
        Fr::from_u256([0xc0df8b81ebff1e57, 0x0c2924ffc64c8c7b, 0x7dceaf28a39b2529, 0x1f95c72f0e35dc68]),
        Fr::from_u256([0x75fad09985f7fb30, 0xfc1ffb6024c2d8d5, 0x01539756b1b6593e, 0x566aa7e50658e0d4]),
        Fr::from_u256([0xebf4a5e203d1adfb, 0xb884d7744fe2c9c1, 0x7a28cbaf719c615e, 0x379687e21e517f4b]),
        Fr::from_u256([0x0da8675d004ed76a, 0x82d8ccc07e156659, 0x65fcee0b7566d520, 0x4bf2f27a3110be0a]),
    ],
    [
        Fr::from_u256([0xeb588626e38c74bb, 0x7acffb9f9059cdfe, 0x752872b2f1f6a982, 0x3cec3f52d6c51ac5]),
        Fr::from_u256([0x1889be54fc3f364f, 0x369754d89e9a4437, 0xa020db4f69bd8956, 0x56826c9ca08d13b7]),
        Fr::from_u256([0x990e3d884d707ea4, 0x7bb475fab00bcb3b, 0x9b07b771f6190b58, 0x131e4bdf35154f40]),
        Fr::from_u256([0xc0bf36a90705af96, 0xcf41a300ba5ff455, 0x3e609641b25384ac, 0x008441f45c5891a2]),
        Fr::from_u256([0xbfa5a79d64c73154, 0x813a2fc3f7e7004b, 0x25794581a9c845ef, 0x2449e60fc62fb475]),
    ],
    [
        Fr::from_u256([0x1d7d011d30eb5b9a, 0x5e9244453b743092, 0xf5d37de54b889e73, 0x20f1b6f5bc5e1de9]),
        Fr::from_u256([0xcf73e9e75d4d5128, 0x81f6dfb6d48b6226, 0xa3b4a0249da859e9, 0x6440d879a180d0c3]),
        Fr::from_u256([0x2ba4e7ee484e2a75, 0xdfb03d0e7a75a659, 0x5ef0700731f0ec45, 0x0f3dde24ba0e030a]),
        Fr::from_u256([0x20b5eb32e95fb9af, 0xf0473b61251dd7be, 0x4b3cd8eb4f4a5ea1, 0x433ab10f1753f78c]),
        Fr::from_u256([0xcb4bc4504387df9d, 0x7131a244e5285b3e, 0x1fb0d5ccdbc1e8ca, 0x31d45e6c117fdef8]),
    ],
    [
        Fr::from_u256([0x5eef45f6e4054c16, 0x33dd383cb9c631d4, 0xd914a63aef3df1e2, 0x14f34648ddbed49f]),
        Fr::from_u256([0xc35c5881cd781f4c, 0xbc70ead93de6f864, 0x67ba2f0d8fdc3f30, 0x13aaac744ad1c6cd]),
        Fr::from_u256([0x76711903643e44bd, 0xd30eb5f9b24791eb, 0x0da510425d5feed1, 0x4db71fa60e8def4b]),
        Fr::from_u256([0x55eb5cbd9deff8b0, 0x59428bdab674d4d3, 0x3c22735aa143207a, 0x3202fe162e61e36b]),
        Fr::from_u256([0x6599fd8ba30b953c, 0xdf2f7c280cff5367, 0x68c7522db5bc8f2d, 0x54533014ac6a4570]),
    ],
    [
        Fr::from_u256([0xf232b174e5741e68, 0x50b6249b5df79429, 0xeb6aafc1efde931d, 0x72537ec2f769abbf]),
        Fr::from_u256([0x6bb60080ea9455af, 0x763f80f54cd8da78, 0x4381b62f944d1cf1, 0x3c568f97e6ab20d4]),
        Fr::from_u256([0xb31686a45b11b2a7, 0x1ed69e24944dbfd6, 0x9913951e64cec394, 0x229df01795187b06]),
        Fr::from_u256([0xeb062b5f9c023eae, 0x5f637137e81b97a4, 0xc07763224b2ecb3a, 0x1b6875b4d7bee6b1]),
        Fr::from_u256([0xdd401887ea44c3d2, 0x3f4974413344d60c, 0xeba723faf9217507, 0x2352f9df2f343196]),
    ],
    [
        Fr::from_u256([0x5a962d3c13d1a306, 0x744a58213224e5f5, 0x30a0dde39405df4b, 0x1f3bc3a3d1651026]),
        Fr::from_u256([0x4dc741a448e41b45, 0xf74db4317236ad1f, 0xdb381c9892d17396, 0x53cdd054262d09f9]),
        Fr::from_u256([0x8d0790cf25bd3caa, 0xc55fcfdd6dea7a3f, 0x0b2327007fff71d0, 0x1a37c2a826eb4ceb]),
        Fr::from_u256([0x78a41e475ac8a28d, 0x8e3803f4bf5393c8, 0xd0e5903ceafca824, 0x3f2871ec67545390]),
        Fr::from_u256([0x99a960e07530c76e, 0xf4fa8be48c9e9df9, 0x814bca621e0fa13e, 0x4929fa218e3bbdec]),
    ],
    [
        Fr::from_u256([0x5a7bdd81d9bf160a, 0xaf009d83848cec98, 0xcde136f4adf2ad62, 0x71d9fb27dfee3244]),
        Fr::from_u256([0xc3aaac212a9a389d, 0x85d7113ef2f7965c, 0x54b298d3fe51b398, 0x2d59a035513255e2]),
        Fr::from_u256([0xca6803eed22b026a, 0x7506c4434877c940, 0x955662d2e1dcc3f4, 0x47dc84e671d05f05]),
        Fr::from_u256([0x303058d29517d31a, 0x22eb45ed6b27e56f, 0x5b601dfb7ace3107, 0x4b133309a3e48696]),
        Fr::from_u256([0x1223716231ff7b20, 0xa076429029e1f036, 0x7cac17c209a612cc, 0x6e0f46fcc17676d1]),
    ],
    [
        Fr::from_u256([0xc59627dcdcf206fa, 0xab1b65be6d443b38, 0x7ce7395e8aa98080, 0x16480a83b20805dd]),
        Fr::from_u256([0xdbd55ba500b99f56, 0x52b6850b45950324, 0x7731bb1ed22ca14b, 0x0cead2326bcc798c]),
        Fr::from_u256([0x0478f3df3c264dfa, 0x31fe7fdc72e44e12, 0x6e7baaa1e6d94fb4, 0x40cb9dd58bf66da3]),
        Fr::from_u256([0xedd7ed26246c3d10, 0x2c8742b16bbb0f61, 0xebf3803d8ea52272, 0x065c0146fde18853]),
        Fr::from_u256([0x6227ac0a332074e6, 0x1246cc2519d76cf2, 0xc1a6ffe9c43b8bac, 0x503ed8a6c6dbb87c]),
    ],
    [
        Fr::from_u256([0xed2fa294dbeae55f, 0xb858e09d31eba641, 0xa4a34cd21ab4437c, 0x39f2bdbe01204c5f]),
        Fr::from_u256([0x23b750e5412b93f9, 0x5d405b7518aa0571, 0x0b6da5b37f6b3eb6, 0x47dc060d8ba7617a]),
        Fr::from_u256([0xf6be77866a0089da, 0xa17727e43e2aa929, 0x55e2f0085b845a5e, 0x6144365b7a4b8e6c]),
        Fr::from_u256([0x406303c197fd114e, 0x8839ab7825c81cfd, 0xe72d78992a3b7770, 0x29a8d242c2e33144]),
        Fr::from_u256([0x8f817cdad23a1022, 0xd59681f4253b7d50, 0x16b95e1ce4469d0b, 0x11cb5c01239eff46]),
    ],
    [
        Fr::from_u256([0x840e4abde050d832, 0xca54472d4aaa9aa5, 0x823e992e75a84e3c, 0x26ee8c0890bf30cc]),
        Fr::from_u256([0x17b01e1fa9834ffd, 0x4bff7acbceb6a49e, 0x33b804012dcfcd51, 0x0857f363b2571525]),
        Fr::from_u256([0xe28b465291cebace, 0xc7b93bd0fe706f6e, 0x77b07c80f6bbe179, 0x27774bed9e59cca5]),
        Fr::from_u256([0x0b5a452fc9e56853, 0xd2dd7b71c6cb06fa, 0x834df31e57330b1b, 0x08f7aa43e01f336e]),
        Fr::from_u256([0xdedd381c4f25cbe4, 0x79a7bc800c8b3856, 0xd2954d9a0bcc99ab, 0x1a69fd6d6655dffa]),
    ],
    [
        Fr::from_u256([0x96d0384ab433d338, 0x0dc602453d5e10a8, 0x2396c0accf95d3f6, 0x2fef9e6487756342]),
        Fr::from_u256([0x3319d9475101638b, 0xa98fd5ab05fa6383, 0x370ee29b8bb14933, 0x31852ce07f5ca50e]),
        Fr::from_u256([0x2a0dfeaa64045b9c, 0xa8e62b4f53cf582c, 0xe633b2516d710d54, 0x130b5eee34b6e1ee]),
        Fr::from_u256([0x6295d662c9720fa1, 0x377e31e00c946862, 0xc14af3a38f9f9262, 0x6abc3ca865756bd3]),
        Fr::from_u256([0x150616ab7ec64708, 0x345ca553401227d0, 0xf933f5d494ed6861, 0x08ad912bf5b568bb]),
    ],
    [
        Fr::from_u256([0xadd83c2c15204345, 0xc677a979dcd15bbb, 0xf352153844c7c2a2, 0x6e036f84ce1f7899]),
        Fr::from_u256([0x9d3108e6da3616e1, 0x71ee5cf05390db9f, 0x4b13583ec7a486f6, 0x5e4918ae69c1efee]),
        Fr::from_u256([0xf86d076adf7d916f, 0xd1ba4fc33d01a390, 0xad40b13283d01708, 0x0effd730ea908bd5]),
        Fr::from_u256([0x2398f6f9dfd1a7d5, 0x8d6a665e11dc4348, 0x971a31a4b78660cb, 0x4dc1a493d56c50b9]),
        Fr::from_u256([0xe4a677454411c718, 0xf41fb315af36febb, 0xeae8021d39c02af7, 0x3bed295c94fabb1a]),
    ],
    [
        Fr::from_u256([0xae522f7ea3def0b5, 0x0bb6cb6a0e6258f5, 0xc8fdc2fe26f2e5dd, 0x22d152a9ef4ab0a1]),
        Fr::from_u256([0x563c2ed87a955651, 0x3842cdd301893d01, 0xf04a9920e71f37cc, 0x309580fd0ba3c798]),
        Fr::from_u256([0x62e022be97ee0db1, 0x13c57b086743de5d, 0xf5f9d51788631b5b, 0x29ce8b5f22cc3809]),
        Fr::from_u256([0x0b235252efb44139, 0x5e5e09facc4fb131, 0xd628c6e619e8dda8, 0x39bba97f5f9ae45f]),
        Fr::from_u256([0x4ff719b052af7b69, 0xba1f652385bf3b79, 0x07fde2b126d31e8d, 0x0de32f53e3079f3c]),
    ],
    [
        Fr::from_u256([0x2670e561e05d727d, 0x0d10bdb7c4c42c3c, 0x41a0b6a8d47ce1a0, 0x4f71cefb6b35efeb]),
        Fr::from_u256([0x5b6d4e7eb660cfc7, 0x7fcd24ab9fd4914a, 0xbda250f5087b2d12, 0x52fceb223a956896]),
        Fr::from_u256([0x73bea51225363207, 0xae497ade7aa9223c, 0xd1f96c0c4361401d, 0x46928f402f591206]),
        Fr::from_u256([0x41b1cf25f3cd958c, 0x0c40e61a49368274, 0xac933198a4e68fd7, 0x4b7b7a3fd342d37a]),
        Fr::from_u256([0x2b09631ad6ea4b56, 0x9769f94a33a80e5b, 0xb5bdd43f8c17eba2, 0x482f326a4e4e74a9]),
    ],
    [
        Fr::from_u256([0xf7aa211e7d0886de, 0x6591f0033a6710c7, 0x5cbb38e53bdb9a35, 0x035f1eeb5804b568]),
        Fr::from_u256([0xc58c96aa3e2ad716, 0x3fe420ff593c0858, 0x6a3594c6c30ce86a, 0x57fbab997196a325]),
        Fr::from_u256([0x1c8e79c3854b354e, 0xe6025c9810bb0eae, 0x903fc90f844456b5, 0x6f21109872981d3a]),
        Fr::from_u256([0xf97666d272c09433, 0x643cf9940e63b2a3, 0x48ec2088af20c5c9, 0x5f6108a1ece25440]),
        Fr::from_u256([0x83545c8f7a1e57da, 0x7869a55651ff925c, 0x5e505f34a952c4cc, 0x3bfce20b1f505d06]),
    ],
    [
        Fr::from_u256([0xd595796ddb7bbb37, 0x4d1633317d5e3474, 0xb73075a7b249adb5, 0x1477b84582d41806]),
        Fr::from_u256([0x4a971913d0fe1ed8, 0x6613bfefa8b12001, 0x47cce526dd47e1de, 0x659245b48b67eeea]),
        Fr::from_u256([0x55e5a4eabeffb5a7, 0x75468455e0645954, 0x8c25f52efc7b381e, 0x4cb3d067e4a938bd]),
        Fr::from_u256([0xc4066e7b127156d8, 0x94a2ee562673e28d, 0xeca4e8223463ea9e, 0x630f8257bef611b0]),
        Fr::from_u256([0xba8b5c088fefad03, 0xcb0a6c26d1db9a5e, 0xea60065036576c8d, 0x0f69ff670df27373]),
    ],
    [
        Fr::from_u256([0x7395fec44ca6ab00, 0x87487f57b52bc700, 0x8b1f1e78e50c22cb, 0x3beb898f874c445b]),
        Fr::from_u256([0x8147c29e4389341c, 0x765e2a0b531e14ce, 0x9465d57d5e470ed9, 0x1e48656fe809a0f0]),
        Fr::from_u256([0x5cde461e20e75cd3, 0x81df36d5a9c8c8d4, 0xd04099905fb12d72, 0x18de052c47f3decf]),
        Fr::from_u256([0x33d1cd30c14170e3, 0x6b20fefa6bf2957e, 0xae03538b7ed3d626, 0x571d08d3639abb65]),
        Fr::from_u256([0x2c67f33f88b91a51, 0x94fecae1fe1f6705, 0xd1ad8b2397f6f085, 0x3e62d040ae04dc46]),
    ],
    [
        Fr::from_u256([0xb1446fe024840a65, 0x97af646b9ad2f011, 0x3b16c78fbed2437c, 0x1684204a247a4897]),
        Fr::from_u256([0xa7ae44a567d277ac, 0x17e842464c6b45e8, 0xfc5d265e66f2ce45, 0x0c03e7b8d8959a92]),
        Fr::from_u256([0x7160aff2ca5f118e, 0x893b81cbae2a4fad, 0x9c1d28b603ac52cd, 0x10c5bbcf92775f4a]),
        Fr::from_u256([0x99adbd28b3fc2832, 0xc0020a40eb34fc1a, 0xc2d0f49ff51dd679, 0x10d3c4e670374791]),
        Fr::from_u256([0xec051993bd12fa14, 0x972f72d8396151ba, 0x9bce763e919eec2a, 0x377252ede0c548bd]),
    ],
    [
        Fr::from_u256([0xd99d07164e7e5e95, 0xeb5a18c6d51def60, 0x916aa56c4447951f, 0x67eeb432b74bd30a]),
        Fr::from_u256([0xb983db5af9664930, 0xbb2f4ef06831af2f, 0x05716111193e59f4, 0x26c2c5587bbc171e]),
        Fr::from_u256([0x64ad8c1dd289280a, 0x0220a74d46671823, 0x5291e129876ab7a5, 0x006b80440301d4ae]),
        Fr::from_u256([0xed92049a1879f1c6, 0x158d567c409904e8, 0xc40f3caffac5782e, 0x04a2b0419d99f4c8]),
        Fr::from_u256([0x947d466484b25b4e, 0x725aecb2ca8b0727, 0x543c72ad42a62e6e, 0x5e2555295579d900]),
    ],
    [
        Fr::from_u256([0x4d857b723af9c1c5, 0xbdf841f2dc70f7fc, 0x78a96854e21fe3c2, 0x36616ff78c391b01]),
        Fr::from_u256([0x43e7526674fb8b93, 0x7c6eeb926870cd6f, 0x3b1e3a52e071448c, 0x272f423888d37333]),
        Fr::from_u256([0x836d37a1a5b49af8, 0xce22c6febb8f82e5, 0x9d7b3bee95c94bd5, 0x34b7a68474770ebe]),
        Fr::from_u256([0x20ef3a03f6c183f4, 0x8f6fc91f7470d30e, 0x2c3809dcdfd92526, 0x00eff85a78e520fe]),
        Fr::from_u256([0xb5c666f21b117997, 0x4518cae7b7bb91d8, 0x87fc463b8683ab3b, 0x092a19b0f8c012c5]),
    ],
    [
        Fr::from_u256([0xb974d14ec10546d6, 0xfae2938025aaeb3f, 0x6af699b8377fdfb5, 0x2a2c165ab5e8db5c]),
        Fr::from_u256([0x0be92ab305b0ee43, 0x8263e6a058290f7a, 0x8fa2de9b4b94e4d2, 0x2b01080281dd7059]),
        Fr::from_u256([0x6711e81c49bf5d48, 0x66eb64b8ee815e61, 0x539993482dd4cb1e, 0x5898aebe423c0698]),
        Fr::from_u256([0x58faf32be095b60e, 0x5f8f0993305491a6, 0xbf7b6438021b761b, 0x4a36019cbc2826ed]),
        Fr::from_u256([0x1957cd012deab20e, 0xeb738897c9296154, 0x31f9413b5474def1, 0x2a4c5c898cdd88c7]),
    ],
    [
        Fr::from_u256([0x867baa910c5dd117, 0x95c498b8f6f8253c, 0x9935342f88985a0d, 0x4ac4354e7a13b014]),
        Fr::from_u256([0x02092ce74dfd309c, 0x9d50770facfa46c5, 0x766d06acabafea9f, 0x5ab8d685c5e76ad6]),
        Fr::from_u256([0x693dd4eb9e4c7b1c, 0xab2ed163654b3ee0, 0x82a5c2436c3a0255, 0x0e9fc998989cb679]),
        Fr::from_u256([0xfd9b6cb1164ac730, 0xb979dc53a2568a86, 0x79c5503915c780fd, 0x582ac3a887e131c7]),
        Fr::from_u256([0x4e985bdc10c271ab, 0x899c4959bd3e52c1, 0x7d242a67284e0f4e, 0x71c19fc34ddf80db]),
    ],
    [
        Fr::from_u256([0x1863f33455adc2c5, 0x6489cdd70afb27b8, 0x43ea79ef65bc4019, 0x07c6cea5a8df6b72]),
        Fr::from_u256([0xbf2534a4263c264b, 0x4790474c661e4670, 0x0c694067c0a18b15, 0x3f33c2f0d53522bc]),
        Fr::from_u256([0x463750d694d5b5e9, 0xf401f089a719ef2a, 0x1111fddc60c67142, 0x59de6d079a1b766b]),
        Fr::from_u256([0x9ca7a25ffe70694c, 0xa5723003ecb8c8da, 0xe263ef8c5a996dc5, 0x58945fc82faaaaa5]),
        Fr::from_u256([0x215742a2a5a4f663, 0x5259ba26bdab5e43, 0x1d5f0abc265786d6, 0x3ff59cc96adc1ccf]),
    ],
    [
        Fr::from_u256([0x116ac77905188ba8, 0x925e57aacf7d2e0a, 0x63cef78bafcb1c61, 0x4d776a4716f5fbe4]),
        Fr::from_u256([0x0f347c6ae8db2a27, 0xdc19a7ce5294c3d4, 0x1aa34fd52d1c6eb8, 0x471bc447b4cd740d]),
        Fr::from_u256([0x16d6c5395281dfba, 0xf53bc263b3f24081, 0x2d2303aa2c4d7c2c, 0x5048fea6f9f14565]),
        Fr::from_u256([0xc97e3524883dc4c8, 0x0e575e42f71e10a9, 0xfba833820b20db78, 0x2f1121c7a7168b25]),
        Fr::from_u256([0x22af83df11d4acb6, 0x07f6dade787ed957, 0xcfbb891808020e36, 0x1f8fce450118f3b7]),
    ],
    [
        Fr::from_u256([0x2b70b92ce11ff535, 0xf88bee9a80f09a54, 0xc73dfdab5e6040e6, 0x67c8d25b50f895bb]),
        Fr::from_u256([0xa442e6594ec85179, 0x6b6e26e781ce113c, 0xa75eac31112a45dd, 0x0d5c2d4bfc2e9135]),
        Fr::from_u256([0xe1f93eb8437c300e, 0x101a0ea64d488a55, 0xe02f672f7c9b103e, 0x310d596e7cc6f220]),
        Fr::from_u256([0x2fd288611a69cebe, 0xfa02a39512476a82, 0xbb28e0028aa9c546, 0x49a5c82cd008f445]),
        Fr::from_u256([0x6ef2fcb06a7db341, 0x40a7dd0f33789d23, 0x494bcec2fc86c3fe, 0x4c8305e86e971e9a]),
    ],
    [
        Fr::from_u256([0x92a9cce9353e850b, 0x18155ec8615e2a39, 0x15f11bc771638793, 0x6fb14a0dd3ca0cc1]),
        Fr::from_u256([0xcaafab416dd68ecf, 0x43b900d9599bc3af, 0xcdf236261ad8f39e, 0x0df212c608d5f57e]),
        Fr::from_u256([0x97d84a634538ebdc, 0x3914954009544097, 0x66d6e02df58a6a10, 0x187ab360c6885cf5]),
        Fr::from_u256([0xa53e78bc3c4a37be, 0x44af61010fd0bc22, 0x82988c2dfb88fe7c, 0x2d51fc1a11a43683]),
        Fr::from_u256([0xd9f5b9eafc6a84ba, 0x0d2a959f1a6d18c5, 0x49953ef609817b4e, 0x3ceac581ca623a1d]),
    ],
    [
        Fr::from_u256([0xecf0f6804c0af19d, 0x22c10579a1e06aad, 0x94b414e8362c52fa, 0x417a8b716fdf62db]),
        Fr::from_u256([0x544f7e7b14d94b18, 0x0aacf35048e2c5f4, 0xf225c3f1f5d62414, 0x25bf9d530eb6c4a9]),
        Fr::from_u256([0x9180702bd539b887, 0xb492b3a7e96ed2b5, 0x33f593424fe2a83e, 0x200c004db152039c]),
        Fr::from_u256([0xce56f9d15d7c7792, 0x11e4c666838bfb1b, 0x167b79b453b54d0b, 0x324078896c34756e]),
        Fr::from_u256([0x0db2a85ee84ae1fb, 0xb62bfbb4337d2c03, 0x8c6c0b1bceac3a97, 0x341bb9252d54c8f6]),
    ],
    [
        Fr::from_u256([0x701f1b00f129aa43, 0xf0818bbc02d10694, 0xdd908368ad6963bf, 0x3b310c5cf096ef56]),
        Fr::from_u256([0xebe56b072caf98f8, 0xde8b6527830c1bb6, 0xe11b9636795f2310, 0x52de48481f2606f5]),
        Fr::from_u256([0x71498ef06fd130b8, 0x3ef00f02b7216f24, 0x6239638a9f61aac4, 0x003e207678b71974]),
        Fr::from_u256([0x0f788c8a88e263f7, 0x1ba03537999e1df2, 0x34fc7f12ace08842, 0x3fcf814e6764ba8e]),
        Fr::from_u256([0x2704e4f46b0c0888, 0x3b96e57094844e0c, 0xac29151995dde7bf, 0x0b501fc361c78071]),
    ],
    [
        Fr::from_u256([0x3e8f242c609a4ba1, 0x20ec95957d115982, 0x061ad106e94aa11a, 0x4516700989d893f3]),
        Fr::from_u256([0xdbf389f04ad3b745, 0x892f3ac4535196bc, 0x686d8be560285a0c, 0x0e397b8050e58bf9]),
        Fr::from_u256([0x3b3c9488d70dab27, 0x9767ee0117cd377f, 0x65445d798d234418, 0x6c20d167d4385a0f]),
        Fr::from_u256([0x2d7de8111fda0bd1, 0x05af3b3525bada3c, 0x4dd9131c62dd13d0, 0x288b9d512a68998e]),
        Fr::from_u256([0x7f69eeae0e7b7c37, 0x4d0b8c27ba444228, 0x687e9296f4b7c023, 0x3339c3baed2c0610]),
    ],
    [
        Fr::from_u256([0x6257873ce700ee30, 0x533a586a0ac10f27, 0x79aad0ba9d5ac322, 0x5fa0cbcc82ce447c]),
        Fr::from_u256([0xdfc9856371bde56a, 0x36ee6d246ee51a6c, 0xcfd989bec0850eda, 0x536f5f63d0c6baed]),
        Fr::from_u256([0x63b3d42010604122, 0x26f4b6e01cc5b916, 0x667ec4737ca9cf30, 0x70f3527cbf13cae9]),
        Fr::from_u256([0xf61ddec34bcbf7c6, 0xe79559f5cdd8243a, 0x3f7edc5471542ace, 0x1f40117fea54fc2a]),
        Fr::from_u256([0x5387ea77c412f072, 0x7c264752761902de, 0xd13a00b7377228ba, 0x495819f08f411313]),
    ],
];

pub const MDS_MATRIX: [[Fr; WIDTH]; WIDTH] = [
    [
        Fr::from_u256([0x132d9207d678c974, 0xe109b8d7e1a94768, 0x85c7fca52bb1d459, 0x4cb6a36f19dea897]),
        Fr::from_u256([0x8050d558b72d7551, 0xdc7c14542badda7a, 0xc165b4b2de0bd8fc, 0x00c53e8eb6c39929]),
        Fr::from_u256([0x13c62041032fe5be, 0x157eee34176ae477, 0xbfa1c17cdcd66258, 0x52ec87116ed097c9]),
        Fr::from_u256([0xc60d217f951d44fa, 0x37d632b8f91173ea, 0x2457467170916baf, 0x6fa53825538d350b]),
        Fr::from_u256([0x37d68dcdf852eeae, 0x7a9951489332ac42, 0xb1b31b52c01b8af2, 0x73a96ab59ee94f11]),
    ],
    [
        Fr::from_u256([0xe2e5829f6ecfd750, 0xdd6b4b7576785e69, 0x4c51986e5cbdbbfa, 0x702b2d525b58e2df]),
        Fr::from_u256([0x4d83a26c65c5e5d0, 0xa305ab55c7131f30, 0x75279c902175dd33, 0x457230bcbe6d5cb0]),
        Fr::from_u256([0x577967d9cb28735b, 0x14cca1bb72660cc9, 0x4d4a6c1c216b8552, 0x3dcd0370a3725dec]),
        Fr::from_u256([0x7b1f4acbefc9dec2, 0xf11e7998893525cc, 0xe2304a2ec03f7a09, 0x28345f3b28ab9773]),
        Fr::from_u256([0x7559833c270b7388, 0xde56f9e57796c56f, 0x0d6907c777e7c79a, 0x361ab54ecfefaa44]),
    ],
    [
        Fr::from_u256([0x8db306c3856acf7c, 0x5eb01ac9e466f6f0, 0x5b5274a84b7978ce, 0x2a83fb9faf301c69]),
        Fr::from_u256([0xd7b38d07520dda16, 0x2e22af03b16441bb, 0x8022e009cbb1b891, 0x28a848ad812e17b9]),
        Fr::from_u256([0x1b8abba8d0c049e1, 0xf49725c300edab33, 0xcec04748242c2939, 0x0dff1ac0b5ad33c8]),
        Fr::from_u256([0xb79b66412a83faf5, 0x1f053a0e54619c63, 0x25745070c90076a4, 0x0c3e764b06b4605e]),
        Fr::from_u256([0x52e923bf13100653, 0xb46a27df45ae44ad, 0x2d0ce86e0d0d39c6, 0x43f858bb7742b383]),
    ],
    [
        Fr::from_u256([0x3e43c120f94ab1ea, 0xd58ad1cecf565108, 0xc98317dae077596b, 0x1d28f98daf2986d8]),
        Fr::from_u256([0x145e91587709439f, 0xce4b26aa6dc476c4, 0x40191205e7277202, 0x441beed75ff1ad77]),
        Fr::from_u256([0xe186cd4f74306b6c, 0xfc3fccd11bfb465d, 0x18b310d87e1b3f75, 0x42e76698f2c64652]),
        Fr::from_u256([0x61182e4383568d1d, 0xe032b89ac639d3e0, 0x751fe8aac048e871, 0x0e2eb5c4c644da6d]),
        Fr::from_u256([0xd0f619b71705a27d, 0x0e42a08edc0737e9, 0x15a8293e9cff3894, 0x527e001ac8252255]),
    ],
    [
        Fr::from_u256([0x46c53851b087cf2e, 0xdf1a5a822d2347a9, 0xdaf7f00a9378146d, 0x191d6a193f1e9848]),
        Fr::from_u256([0x2a6fb104d0b72cfb, 0xade06daee7615608, 0xe2e5920f7809ee72, 0x47696f503327d47f]),
        Fr::from_u256([0xb76e2bfa06585bfc, 0x686bcbbcdbfa4012, 0x0f7866f90c76e778, 0x0b24c2b73f9283e5]),
        Fr::from_u256([0x2dc7d5e9d62f81ef, 0x7bacd942a81b2698, 0x990a0d1b115e5e89, 0x1a3d727aedd620ae]),
        Fr::from_u256([0x8791186c07d2d718, 0x2ec4c1b547dc11e3, 0xc5749c35b7fe4763, 0x3fe9a40ab3efb27f]),
    ],
];

pub const INITIAL_MDS_MATRIX: [[Fr; WIDTH]; WIDTH] = [
    [ONE, ZERO, ZERO, ZERO, ZERO],
    [ZERO, ONE, ZERO, ZERO, ZERO],
    [ZERO, ZERO, ONE, ZERO, ZERO],
    [ZERO, ZERO, ZERO, ONE, ZERO],
    [ZERO, ZERO, ZERO, ZERO, ONE],
];

pub fn perm(input: &[Fr; WIDTH]) -> [Fr; WIDTH] {
    let mut state = input.clone();
    let mut temp_state;
    for (r, c) in ROUND_CONSTANTS.iter().enumerate() {
        for i in 0..WIDTH {
            state[i] += c[i];
        }
        for i in 0..if r < R_F / 2 || r >= R_F / 2 + R_P { WIDTH } else { 1 } {
            state[i] = state[i].pow([5]);
        }
        temp_state = state.clone();
        for i in 0..WIDTH {
            state[i] = ZERO;
            for j in 0..WIDTH {
                state[i] += MDS_MATRIX[i][j] * temp_state[j];
            }
        }
    }
    state
}

pub struct PoseidonCircuit {
    pub preimage: [Fr; WIDTH],
}

impl PoseidonCircuit {
    pub fn perm<CS: ConstraintSystem<Bls12>>(
        cs: &mut CS,
        state_scalar: &[Fr; WIDTH],
        state_var: &[Variable; WIDTH],
    ) -> ([Fr; WIDTH], [Variable; WIDTH]) {
        let mut state_scalar = *state_scalar;
        let mut state_var = *state_var;
        for (r, c) in ROUND_CONSTANTS.iter().enumerate() {
            let mds_matrix = if r == 0 { INITIAL_MDS_MATRIX } else { MDS_MATRIX };
            let temp_state_var = state_var.clone();
            let temp_state_scalar = state_scalar.clone();
            for i in 0..WIDTH {
                let mut lc = LinearCombination::zero();
                state_scalar[i] = ZERO;
                for j in 0..WIDTH {
                    state_scalar[i] += mds_matrix[i][j] * temp_state_scalar[j];
                    lc = lc + (mds_matrix[i][j], temp_state_var[j]);
                }
                state_scalar[i] += c[i];
                lc = lc + (c[i], CS::one());
                if i == 0 || r < R_F / 2 || r >= R_F / 2 + R_P {
                    let square_scalar = state_scalar[i] * state_scalar[i];
                    let square_var = alloc(cs, square_scalar);
                    cs.enforce(
                        || format!("Round {0} (full), state[{1}]^2", r, i),
                        |_| lc.clone(),
                        |_| lc.clone(),
                        |lc| lc + square_var,
                    );
                    let quad_scalar = square_scalar * square_scalar;
                    let quad_var = alloc(cs, quad_scalar);
                    cs.enforce(
                        || format!("Round {0} (full), state[{1}]^4", r, i),
                        |lc| lc + square_var,
                        |lc| lc + square_var,
                        |lc| lc + quad_var,
                    );
                    state_scalar[i] = state_scalar[i] * quad_scalar;
                    let quint_var = alloc(cs, state_scalar[i]);
                    cs.enforce(
                        || format!("Round {0} (full), state[{1}]^5", r, i),
                        |_| lc,
                        |lc| lc + quad_var,
                        |lc| lc + quint_var,
                    );
                    state_var[i] = quint_var;
                } else {
                    let v = alloc(cs, state_scalar[i]);
                    cs.enforce(
                        || format!("Round {0} (partial), state[{1}]", r, i),
                        |_| lc,
                        |lc| lc + CS::one(),
                        |lc| lc + v,
                    );
                    state_var[i] = v;
                }
            }
        }

        let temp_state_scalar = state_scalar.clone();
        let temp_state_var = state_var.clone();
        for i in 0..WIDTH {
            let mut state_lc = LinearCombination::zero();
            state_scalar[i] = ZERO;
            for j in 0..WIDTH {
                state_scalar[i] += MDS_MATRIX[i][j] * temp_state_scalar[j];
                state_lc = state_lc + (MDS_MATRIX[i][j], temp_state_var[j]);
            }
            let v = alloc(cs, state_scalar[i]);
            cs.enforce(|| "Final round", |_| state_lc, |lc| lc + CS::one(), |lc| lc + v);
            state_var[i] = v;
        }
        (state_scalar, state_var)
    }
}

impl Circuit<Bls12> for PoseidonCircuit {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let state_scalar = self.preimage;
        let state_var = self.preimage.map(|i| alloc(cs, i));
        let (state_scalar, state_var) = Self::perm(cs, &state_scalar, &state_var);
        for i in 0..WIDTH {
            let input_var = alloc_input(cs, state_scalar[i]);
            cs.enforce(
                || "Final round",
                |lc| lc + input_var,
                |lc| lc + CS::one(),
                |lc| lc + state_var[i],
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bellperson::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof};
    use rand::thread_rng;

    use super::*;

    #[test]
    fn test_poseidon_perm() {
        let mut input = [ZERO; WIDTH];
        for i in 0..WIDTH {
            input[i] = Fr::from_repr(FrRepr::from(i as u64)).unwrap();
        }
        assert_eq!(
            perm(&input),
            [
                Fr::from_u256([15920028650651433979, 15367630617372052945, 16842072888235855925, 5364183568613355987]),
                Fr::from_u256([753299389160023627, 8523200757953221596, 13900257748706808915, 7432604917176123505]),
                Fr::from_u256([18185073430223728475, 13832025790910041910, 7512623282274586504, 460794977886672672]),
                Fr::from_u256([7295251966227533110, 12018110873688808699, 15334287645997493894, 2786942240109759229]),
                Fr::from_u256([166014608257070160, 13187367121313192971, 14302507254012785838, 1685505972388993413]),
            ]
        );
    }

    #[test]
    fn test_poseidon_perm_zk() {
        let params = generate_random_parameters::<Bls12, _, _>(
            PoseidonCircuit {
                preimage: [ZERO; WIDTH],
            },
            &mut thread_rng(),
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);

        let mut input = [ZERO; WIDTH];
        for i in 0..WIDTH {
            input[i] = Fr::random(&mut thread_rng());
        }

        let proof = create_random_proof(PoseidonCircuit { preimage: input }, &params, &mut thread_rng()).unwrap();

        assert!(verify_proof(&pvk, &proof, &perm(&input)).unwrap());
    }
}
