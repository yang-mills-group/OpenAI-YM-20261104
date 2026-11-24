import YM.Integration.WilsonPositionScaleLawBounded
import YM.Integration.WilsonPositionScaleLawKinetic

/-! In the actual declared position equations, the independent MS scale matrix
cancels the dilated position bank to every requested order, uniformly in ratio.
The only remainder is the explicitly bounded finite set of overflow products. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawPolynomial
open Function Set Filter Finset PowerSeries Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawIndependent (B trial scaleRows)
open WilsonPhysicalPositionDiscreteBranches (field)
open scoped BigOperators Topology Classical
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

abbrev logRatio:=WilsonPositionScaleLawIndependent.time

def pre (d q:ℕ)(t:Ratio)(g:ℝ):Prediction G d:=
  ∑k:Fin (q+1),(g:ℂ)^k.val • scaleRows Z M ν d (logRatio t) k.val

private def post (d q:ℕ)(t:Ratio)(g:ℝ):Prediction G d:=
  ∑k∈range (q+1),g^k • realm (B Z M ν (logRatio t) d) (scaleRows Z M ν d (logRatio t)) k

theorem rows (d q:ℕ)(t:Ratio)(g:ℝ){n:ℕ}(v:Fin n→Sec G d)(φ:Test n):
    pre Z M ν d q t g n φ v=∑k:Fin (q+1),(g:ℂ)^k.val * scaleRows Z M ν d (logRatio t) k.val n φ v:=by
  simp only [pre,Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,_root_.sum_apply,
    LinearMap.smul_apply,_root_.smul_apply,smul_eq_mul]

include H in
private theorem atPost (d q:ℕ)(t:Ratio)(g:ℝ):(Z.store.measure d).D (post Z M ν d q t g)=
    (Z.store.measure d).D (reference G d):=by
  simp only [post,map_sum,map_smul,WilsonPositionScaleLawIndependent.solved Z M H ν,smul_ite,smul_zero,
    Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,if_true,pow_zero,one_smul]

private theorem watchPost (d q:ℕ)(t:Ratio)(g:ℝ)(W:Window G d):
    watch W (post Z M ν d q t g)=∑k∈range (q+1),(g:ℂ)^k * realm (B Z M ν (logRatio t) d)
      (scaleRows Z M ν d (logRatio t)) k W.n W.t W.p:=by
  rw [post,map_sum]
  apply sum_congr rfl;intro i _;rw [map_smul,Complex.real_smul,Complex.ofReal_pow];rfl

private theorem stamped {d:ℕ}(P:Prediction G d): (Z.store.survey d).stamps
    (fun i=>watch ((Z.store.survey d).scope i) P)=guide G d ((Z.store.measure d).D P):=by
  change guide G d ((Z.store.survey d).tally _)=_;rw [(Z.store.survey d).equal]

private theorem atFree (d:ℕ):(Z.store.survey d).itinerary (Z.store.survey d).opening=
    guide G d ((Z.store.measure d).D (reference G d)):=by
  change (Z.store.survey d).itinerary ((Z.store.survey d).purse _,0)=_
  rw [(Z.store.survey d).way]
  have one:recruit (Fray.box (0:MoveSpace G d)) (reference G d)=reference G d:=by
    rw [Fray.box,map_zero,stand0];rfl
  rw [one]

include H in
theorem original (d q:ℕ):∃C:ℝ,0≤C ∧ ∀t:Ratio,∀g:ℝ,|g|≤1→
    let D:=Z.store.survey d
    ‖D.itinerary (D.purse (pre Z M ν d q t g),trial Z M ν d q (logRatio t) g)-D.itinerary D.opening‖≤C*|g|^(q+1):=by
  let D:=Z.store.survey d
  let run(t:Ratio)(g:ℝ):=recruit (field (trial Z M ν d q (logRatio t) g)) (pre Z M ν d q t g)
  let due(t:Ratio)(g:ℝ)(i:Fin D.n):=watch (D.scope i) (run t g)-watch (D.scope i) (post Z M ν d q t g)
  have atScope (i:Fin D.n):∃c:ℝ,0≤c ∧ ∀t:Ratio,∀g:ℝ,|g|≤1→‖due t g i‖≤c*|g|^(q+1):=by
    let w:=D.scope i
    obtain ⟨c,hc,bound⟩:=WilsonPositionScaleLawBounded.omitted Z M H ν q w.t w.p
    refine ⟨c,hc,fun t g hg=>?_⟩
    change ‖pre Z M ν d q t g w.n w.t (fun j=>field (trial Z M ν d q (logRatio t) g) (w.p j))-
      watch w (post Z M ν d q t g)‖≤_
    rw [rows,watchPost];simp_rw [WilsonPositionScaleLawKinetic.field Z M H ν]
    exact bound t g hg
  choose c hc spent using atScope
  let A:=∑i,c i
  have hA:0≤A:=sum_nonneg fun i _=>hc i
  refine ⟨‖D.stamps‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
  intro t g hg
  have billed:D.itinerary (D.purse (pre Z M ν d q t g),trial Z M ν d q (logRatio t) g)-D.itinerary D.opening=
      D.stamps (due t g):=by
    rw [D.way,atFree,←atPost Z M H ν d q t g]
    change guide G d ((Z.store.measure d).D (run t g))-_=_
    rw [←stamped,←stamped,←map_sub];rfl
  change ‖D.itinerary (D.purse _,_)-D.itinerary D.opening‖≤_
  rw [billed,mul_assoc]
  refine (D.stamps.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA (pow_nonneg (abs_nonneg g) _))).2
  exact fun i=>(spent i t g hg).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=c) (fun j _=>hc j) (mem_univ i))
    (pow_nonneg (abs_nonneg _) _))

end YM.Integration.WilsonPositionScaleLawPolynomial
end
