import YM.Integration.WilsonOriginalOccupiedSource

/-! The erased tap is the true original vacuum times the entire ordinary lamp product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedWallet
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open WilsonOriginalOccupiedTap WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {P:Rep G n} {o:V→Site n} {X ι:Type}
theorem origin (A:Gallery X ι o P R) (x:X) (U:Config G n) (w:V→ℝ) (wp:∀v,0<w v)
    {B:ℝ} (fund:(gallery 0 A).K.Paid w P.p.B P.p.supportExponent B):
    (gallery 0 A).density x U=(P.eval U:ℂ) • Poly.pass (A.E.log x U) :=by
  let H:=(gallery 0 A).K
  have row (i):H.hard x i U=Poly.bead R (P.activities.K i U:ℂ):=by
    ext1 s
    rw [show (H.hard x i U).part s=if s=R.quiet then (P.activities.K i U:ℂ) else 0
      from WilsonOriginalOccupiedTap.origin A.K x i U s]
    simp [Poly.bead,Poly.part_send]
  have cover (l:Finset ℕ): (∏ i∈l,H.hard x i U)=Poly.bead R (∏i∈l,(P.activities.K i U:ℂ)):=by
    calc
      _ = ∏i∈l,Poly.bead R (P.activities.K i U:ℂ):=
        Finset.prod_congr rfl fun i _=>row i
      _ = _ := (map_prod (Poly.bead R) (fun i=>(P.activities.K i U:ℂ)) l).symm
  have sm:=Hard.packet_summing _ fund P.p.exponent_pos.le wp x U
  have base:(gallery 0 A).gas x U=Poly.bead R (P.activities.gas P.p U:ℂ):=by
    ext1 s
    by_cases eq:s=R.quiet
    · subst s
      exact (Hard.packet_of_quiet _ x U sm).trans (by simp [Poly.bead,Poly.part_send])
    · rw [show ((gallery 0 A).gas x U).part s=∑'l,(Attached.packet P.activities P.p (H.hard x) U l).part s
        from Poly.share sm s]
      have off (l): (Attached.packet P.activities P.p (H.hard x) U l).part s=0:=by
        unfold Attached.packet
        split
        · rw [cover]; change (Poly.send R.quiet _).part s=0; rw [Poly.part_send,if_neg eq]
        · rfl
      simp [off,Poly.bead,Poly.part_send,eq]
  rw [Gallery.density,base,mul_comm,Poly.product_bead,smul_smul]
  rw [Rep.eval,Complex.ofReal_mul]
  rfl


def inverseAmplitude (n:ℕ)(κ:ℝ):ℝ:=4*n*κ

omit [Fintype V] in
theorem enrolled (A:Gallery X ι o P R) (w:V→ℝ)(wp:∀v,0<w v)
    (k:ℕ)(positive:0<k) (κ:ℝ)(kp:0<κ)(small:inverseAmplitude k κ ≤ 1)
    (hard:A.K.Paid w P.p.B P.p.supportExponent κ):
    let q:=inverseAmplitude k κ
    let T:=q⁻¹
    ∀z∈nodes k (T:ℂ),(gallery z A).K.Paid w P.p.B P.p.supportExponent 1:=by
  dsimp only
  let q:=inverseAmplitude k κ
  have hq:0<q:=by dsimp [q,inverseAmplitude];positivity
  have kn:1 ≤ (k:ℝ):=by exact_mod_cast positive
  have lt:1 ≤ q⁻¹:=(one_le_inv₀ hq).2 small
  let m:=(k:ℝ)*q⁻¹
  have hm:1 ≤ m:=one_le_mul_of_one_le_of_one_le kn lt
  have cost:m*κ ≤ 1:=by
    dsimp [m,q,inverseAmplitude]
    have hk:(k:ℝ)≠0:=by positivity
    field_simp
    nlinarith
  intro z hz
  have cap:‖z‖ ≤ m:=by
    rcases mem_insert.mp hz with rfl|hz
    · simpa using hm
    rcases mem_insert.mp hz with rfl|hz
    · simpa using (zero_le_one.trans hm)
    obtain ⟨i,_,rfl⟩:=mem_image.mp hz
    change ‖((q⁻¹:ℝ):ℂ)*node i‖ ≤ m
    have hi:(i.val:ℝ) ≤ k:=by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    simp only [node,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hq),
      Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hq.le)).trans_eq (mul_comm ..)
  exact Hard.mono _ (WilsonOriginalOccupiedTap.paid A.K z hm cap wp hard) cost

end YM.Integration.WilsonOriginalOccupiedWallet
