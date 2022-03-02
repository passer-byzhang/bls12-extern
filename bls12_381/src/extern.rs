use crate::fp::*;
use crate::fp12::*;
use crate::fp2::*;
use crate::fp6::*;
use crate::g1::*;
use crate::g2::*;
use crate::pairings::{multi_miller_loop, pairing, G2Prepared, Gt, MillerLoopResult};

pub fn g1_to_bytes(g1: G1Affine) -> [u8; 96] {
    g1.to_uncompressed()
}

pub fn bytes_to_g1(bytes: [u8; 96]) -> G1Affine {
    G1Affine::from_uncompressed(&bytes).unwrap()
}

pub fn g2_to_bytes(g2: G2Affine) -> [u8; 192] {
    g2.to_uncompressed()
}

pub fn bytes_to_g2(bytes: [u8; 192]) -> G2Affine {
    G2Affine::from_uncompressed(&bytes).unwrap()
}

pub fn gt_to_bytes(result: Gt) -> [u64; 72] {
    let mut vec_fp = [0u64; 72];
    let fp12 = result.0;
    let fp0_0_0 = fp12.c0.c0.c0.0;
    let fp0_0_1 = fp12.c0.c0.c1.0;
    let fp0_1_0 = fp12.c0.c1.c0.0;
    let fp0_1_1 = fp12.c0.c1.c1.0;
    let fp0_2_0 = fp12.c0.c2.c0.0;
    let fp0_2_1 = fp12.c0.c2.c1.0;
    let fp1_0_0 = fp12.c1.c0.c0.0;
    let fp1_0_1 = fp12.c1.c0.c1.0;
    let fp1_1_0 = fp12.c1.c1.c0.0;
    let fp1_1_1 = fp12.c1.c1.c1.0;
    let fp1_2_0 = fp12.c1.c2.c0.0;
    let fp1_2_1 = fp12.c1.c2.c1.0;
    vec_fp[0..6].copy_from_slice(&fp0_0_0);
    vec_fp[6..12].copy_from_slice(&fp0_0_1);
    vec_fp[12..18].copy_from_slice(&fp0_1_0);
    vec_fp[18..24].copy_from_slice(&fp0_1_1);
    vec_fp[24..30].copy_from_slice(&fp0_2_0);
    vec_fp[30..36].copy_from_slice(&fp0_2_1);
    vec_fp[36..42].copy_from_slice(&fp1_0_0);
    vec_fp[42..48].copy_from_slice(&fp1_0_1);
    vec_fp[48..54].copy_from_slice(&fp1_1_0);
    vec_fp[54..60].copy_from_slice(&fp1_1_1);
    vec_fp[60..66].copy_from_slice(&fp1_2_0);
    vec_fp[66..72].copy_from_slice(&fp1_2_1);
    vec_fp
}

pub fn bytes_to_fp2(bytes: [u64; 12]) -> Fp2 {
    let mut fp0 = [0u64; 6];
    fp0[0..6].copy_from_slice(&bytes[0..6]);
    let mut fp1 = [0u64; 6];
    fp1[0..6].copy_from_slice(&bytes[6..12]);
    Fp2 {
        c0: Fp(fp0),
        c1: Fp(fp1),
    }
}

pub fn bytes_to_gt(bytes: [u64; 72]) -> Gt {
    let mut fp0_0 = [0u64; 12];
    fp0_0[0..12].copy_from_slice(&bytes[0..12]);
    let fp0_0 = bytes_to_fp2(fp0_0);

    let mut fp0_1 = [0u64; 12];
    fp0_1[0..12].copy_from_slice(&bytes[12..24]);
    let fp0_1 = bytes_to_fp2(fp0_1);

    let mut fp0_2 = [0u64; 12];
    fp0_2[0..12].copy_from_slice(&bytes[24..36]);
    let fp0_2 = bytes_to_fp2(fp0_2);

    let mut fp0 = Fp6 {
        c0: fp0_0,
        c1: fp0_1,
        c2: fp0_2,
    };
    let mut fp1_0 = [0u64; 12];
    fp1_0[0..12].copy_from_slice(&bytes[36..48]);
    let fp1_0 = bytes_to_fp2(fp1_0);

    let mut fp1_1 = [0u64; 12];
    fp1_1[0..12].copy_from_slice(&bytes[48..60]);
    let fp1_1 = bytes_to_fp2(fp1_1);

    let mut fp1_2 = [0u64; 12];
    fp1_2[0..12].copy_from_slice(&bytes[60..72]);
    let fp1_2 = bytes_to_fp2(fp1_2);

    let fp1 = Fp6 {
        c0: fp1_0,
        c1: fp1_1,
        c2: fp1_2,
    };

    Gt(Fp12 { c0: fp0, c1: fp1 })
}

fn bytes_multi_miller_loop(g1_bytes: [u8; 96], g2_bytes: [u8; 192]) -> [u64; 72] {
    let g1 = G1Affine::from_uncompressed(&g1_bytes).unwrap();
    let g2 = G2Affine::from_uncompressed(&g2_bytes).unwrap();
    let g2_pre = G2Prepared::from(g2);
    let result = multi_miller_loop(&[(&g1, &g2_pre)]).final_exponentiation();
    gt_to_bytes(result)
}

pub fn bytes_pairing(g1_bytes: [u8; 96], g2_bytes: [u8; 192]) -> [u64; 72] {
    let g1affine = G1Affine::from_uncompressed(&g1_bytes).unwrap();
    let g2affine = G2Affine::from_uncompressed(&g2_bytes).unwrap();
    let result = pairing(&g1affine, &g2affine);
    gt_to_bytes(result)
}

#[test]
fn test_g_serialize_deserialize() {
    let g1_identity = G1Affine::identity();
    let g1_bytes = g1_to_bytes(g1_identity);
    let g1_test = bytes_to_g1(g1_bytes);

    let g2_identity = G2Affine::identity();
    let g2_bytes = g2_to_bytes(g2_identity);
    let g2_test = bytes_to_g2(g2_bytes);

    let result = MillerLoopResult::default().final_exponentiation();
    let result_bytes = gt_to_bytes(result);
    let result_test = bytes_to_gt(result_bytes);

    assert_eq!(g2_identity.eq(&g2_test), true);
    assert_eq!(g1_identity.eq(&g1_test), true);
    assert_eq!(result.0.eq(&result_test.0), true);
}

#[test]
fn test_bytes_multi_miller_loop() {
    let g1 = G1Affine::from(G1Projective::generator());
    let g2 = G2Affine::from(G2Projective::generator());
    let g2_pre = G2Prepared::from(g2);
    let result = multi_miller_loop(&[(&g1, &g2_pre)]).final_exponentiation();

    let g1_bytes = g1_to_bytes(g1);
    let g2_bytes = g2_to_bytes(g2);

    let result_bytes = bytes_multi_miller_loop(g1_bytes, g2_bytes);
    let result_test = bytes_to_gt(result_bytes);

    assert_eq!(result.0.eq(&result_test.0), true);
}

fn bytes_gt_add(a: [u64; 72], b: [u64; 72]) -> [u64; 72] {
    let a = bytes_to_gt(a);
    let b = bytes_to_gt(b);
    gt_to_bytes(a + b)
}

#[test]
fn test_bytes_pairing_loop() {
    let a1 = G1Affine::generator();
    let b1 = G2Affine::generator();
    let b1_prepared = G2Prepared::from(b1);

    let expected = pairing(&a1, &b1);
    let test =
        multi_miller_loop(&[(&a1, &b1_prepared), (&a1, &b1_prepared)]).final_exponentiation();
    let result_pairings = expected + expected;
    assert_eq!(result_pairings.0, test.0);
}

#[test]
fn test_bytes_pairing() {
    let g1 = G1Affine::from(G1Projective::generator());
    let g2 = G2Affine::from(G2Projective::generator());
    let g2_pre = G2Prepared::from(g2);
    let result = pairing(&g1, &g2);

    let g1_bytes = g1_to_bytes(g1);
    let g2_bytes = g2_to_bytes(g2);
    let result_bytes = bytes_pairing(g1_bytes, g2_bytes);
    let result_test = bytes_to_gt(result_bytes);
    let result_loop = multi_miller_loop(&[(&g1, &g2_pre)]).final_exponentiation();
    assert_eq!(result.0, result_loop.0);
    assert_eq!(result.0.eq(&result_test.0), true);
}
