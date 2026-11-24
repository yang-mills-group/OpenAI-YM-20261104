import YM.Integration.WilsonSeparatedMovingCells
import YM.Integration.WilsonSeparatedForwardFrame
import YM.Integration.IntrinsicWilsonRoom
import YM.Integration.IntrinsicWilsonTensor
import YM.OPE.Short.Vacuum
import YM.RG12.Kintsugi.Spot

/-! The true zero-horizon pivot/mixed Gram is an entire input roster.
Its single varying captured cutoff tensor precedes the physical choice
in every input, including the choices of earlier reporting lengths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedDiagnosticGram
open Function Filter Set Lattice Wilson Cells Spec Climb OPE OPE.Orbits OPE.Cards OPE.Log OPE.Nesting PhysMS
open Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open Next.UVStress
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ}

private abbrev empty (S : Table C.book) (z : Empty) : S.Tag := Short.extra (z:=z)

/-- The numerical coefficient of the physical unit at zero output horizon. -/
def scalar (S T : Table C.book) : S.Field 0 →ₗ[ℂ] ℂ :=
  upon T 0 0 Short.gapPos (voices (empty S))

theorem unit (F : Final C f S) (hG : G.Simple) (q : Viewers F) (z : S.Field 0) :
    scalar S (spectator F q) z • S.unit 0 = z := by
  obtain ⟨c,rfl⟩ := RG12.Kintsugi.Spot.unit_desc (C:=C) (S:=S) hG (by norm_num : (0:ℕ)<4) z
  rw [map_smul,show scalar S (spectator F q) (S.unit 0)=1 from Short.vacuum F q 0 0 (empty S)]
  rw [smul_eq_mul,mul_one]

private theorem commonScalar (F : Final C f S) (hG : G.Simple) (q : Viewers F) (z:S.Field 0) :
    scalar S (spectator F q) z=scalar S S z := by
  exact smul_left_injective ℂ (S.alive 0 F.room.kernel.laws)
    ((unit F hG q z).trans (unit F hG none z).symm)

private theorem columns (d:I→ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ m : MultilinearMap ℂ (fun i=>Input C (d i)) ℂ, ∀ b : ℝ,
      (∀ a : Code (fun i=>Input C (d i)),‖m (combination _ a)‖≤b) →
      ∀ v,‖m v‖≤B*b*(∏ i,‖v i‖) := by
  classical
  let P (i:I) := Input C (d i)
  let coord (a : Code P) (i:I) := ((Module.finBasis ℂ (P i)).coord (a i)).toContinuousLinearMap
  let size (a : Code P) := ∏ i,‖coord a i‖
  have sn (a : Code P) : 0 ≤ size a := Finset.prod_nonneg fun _ _=>ContinuousLinearMap.opNorm_nonneg _
  have invoice (a:Code P) (v:(i:I)→P i) : ‖coords P a v‖ ≤ size a*∏ i,‖v i‖ := by
    unfold coords size
    rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(coord a i).le_opNorm _)
  refine ⟨∑ a:Code P,size a,Finset.sum_nonneg (fun a _=>sn a),?_⟩
  intro m b raw v
  let p := ∏ i,‖v i‖
  have positive : 0≤p := Finset.prod_nonneg fun i _=>norm_nonneg _
  rw [basis_tuple P v m]
  calc
    _ ≤ ∑ a:Code P,‖coords P a v*m (combination P a)‖ := norm_sum_le ..
    _ ≤ ∑ a:Code P,size a*(b*p) := Finset.sum_le_sum fun a _=>by
      rw [norm_mul]
      exact (mul_le_mul (invoice a v) (raw a) (norm_nonneg _) (mul_nonneg (sn a) positive)).trans_eq (by ring)
    _ = (∑ a:Code P,size a)*(b*p) := (Finset.sum_mul ..).symm
    _ = _ := (mul_assoc ..).symm

/-- The unselected and permitted character readings use the same common
actual regulator limit Z, which precedes arbitrary incoming vectors. -/
theorem diagnostic (F : Final C f S) (fac : Facilities C f S) (anchor:I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C 0 (Fintype.card I) (∑ i,d i)) (J : ℝ → tower S) (H : Leading F J)
    {M η σ : ℝ} (ηp : 0<η) (roomFor : σ<1/32) {g : ℝ → ℝ} (hg : Coupling G g)
    (k:ℕ) {ε:ℝ} (εp : 0<ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, WithinRoom r M η (C.S.gridPoint (P.j r) ∘ x) 0 →
      (∃ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z) ∧
      ∀ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z →
        let y := C.S.gridPoint (P.j r) ∘ x
        ∀ q : Viewers F,q=none ∨ Screen y → ∀ v : (i:I)→Input C (d i),
          ‖Orbits.moment (spectator F q) y (Frame.born J r v)-scalar S S (S.project 0 (Z v))‖ ≤
            ε*g r^k*r^σ*∏ i,‖v i‖ := by
  classical
  let X (i:I) := Input C (d i)
  obtain ⟨B,nb,invoice⟩ := columns (C:=C) d
  let ε' := ε/(B+1)
  have ε'p : 0<ε' := div_pos εp (by linarith only [nb])
  have coupon : B*ε'≤ε := by
    dsimp only [ε']
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith only [nb])).mpr
    nlinarith only [εp.le]
  let b := P.h/4
  have bp : 0<b := div_pos P.pos (by norm_num)
  have inner : 3*b<P.h := by dsimp only [b]; linarith only [P.pos]
  let gas := empty S
  have paid (a : Code X) := WilsonSeparatedMovingCells.original F fac anchor Q P J H (combination X a) hg fac.simpleGate
    (degrees gas) (fun _=>1) (fun _=>zero_lt_one) bp inner σ (by simpa only [Finset.univ_eq_empty,
      Finset.sum_empty,add_zero] using roomFor) k ε' ε'p
  filter_upwards [eventually_all.mpr paid,IntrinsicWilsonRoom.admits (I:=I) P M η ηp,
    common F fac anchor Q P J H,length_rate.pos,hg.positive] with r entries admit obtainZ rp gp
  change 0<r at rp
  intro x room
  have plot := admit x room
  refine ⟨obtainZ x plot,?_⟩
  intro Z commonZ y q character v
  have inside : Injective y := by
    intro i j eq
    by_contra ne
    have h := room.spaced i j ne
    change η*r≤‖y i-y j‖ at h
    rw [eq,sub_self,norm_zero] at h
    exact (mul_pos ηp rp).not_ge h
  have besideClear : Injective (beside y Short.gapPos) :=
    beside_distinct.mpr ⟨inside,injective_of_subsingleton _,fun _ j=>nomatch j⟩
  have clear : ClearOf 0 Short.gapPos (r^b) := by constructor <;> intro i <;> cases i
  let Xnear := (Orbits.moment (spectator F q) (S:=S) (d:=d) y).compLinearMap (fun i=>(J r (d i)).toLinearMap)
  let compare := Xnear - (scalar S S).compMultilinearMap ((S.project 0).compMultilinearMap Z)
  let debt := ε'*g r^k*r^σ
  have rows (a:Code X) : ‖compare (combination X a)‖ ≤ debt := by
    let w := combination X a
    let ins := Frame.born J r w
    have deliver := (entries a x plot).2 (Z w) (commonZ.cluster w) Short.gapPos clear besideClear
      (voices gas) (fun i=>nomatch i)
    have equation : whole (spectator F q) y ins Short.gapPos (voices gas) =
        Orbits.moment (spectator F q) y ins := Short.tagged F (Orbits.tags ins) y q inside
    change ‖Orbits.moment (spectator F q) y ins-scalar S S (S.project 0 (Z w))‖ ≤ _
    rw [←equation,←commonScalar F fac.simpleGate q]
    have bought :
        ‖whole (spectator F q) y ins Short.gapPos (voices gas)-scalar S (spectator F q) (S.project 0 (Z w))‖ ≤
          ε'*g r^k*r^0*r^σ := by
      rcases character with rfl|s
      · exact deliver.1
      · exact deliver.2 s q
    simpa only [pow_zero,mul_one] using bought
  have finish := invoice compare debt rows v
  apply finish.trans
  have pos : 0≤g r^k*r^σ := mul_nonneg (pow_nonneg gp.le _) (Real.rpow_nonneg rp.le _)
  have positive : 0 ≤ ∏ i,‖v i‖ := Finset.prod_nonneg fun i _=>norm_nonneg (v i)
  have final := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coupon pos) positive
  simpa only [debt,mul_assoc] using final

end YM.Integration.WilsonSeparatedDiagnosticGram
