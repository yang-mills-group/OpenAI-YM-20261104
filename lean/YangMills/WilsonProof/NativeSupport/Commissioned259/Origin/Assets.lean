import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Inquiry
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Layers
/-! # D, c, Y costs of (G.6). Maintain all phases. No changing Horizon to
force singular value payment here. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {I J K : Type}[Fintype I][Fintype K]{l : Filter J} {s r : J→ℝ}
    (hs : Tendsto s l late)
    {x:J→ I→E4} {y:J→ K→E4}{o:J→ E4} {M δ:ℝ}(mn:0≤M)(dp:0<δ)
    (hx : ∀ᶠ i in l,Flash259HorizonFork.Ready (r i) (s i) M δ (x i) (y i))
    {d:I→ℕ}{e:K→ℕ} {u:J→(i:I)→Sec G (d i)}{v:J→(j:K)→Sec G (e j)}
    (hu:∀ (i:I) (b:Toon G (d i)),Allowance l r (fun _=>1) (fun j=>coord b (u j i)))
    (hv:∀ (i:K) (b:Toon G (e i)),Allowance l r (fun _=>1) (fun j=>coord b (v j i)))
    (p:J→Viewers F) {h:ℕ}
local notation "U" => (fun i=>enter Z (r i) (u i))
local notation "V" => (fun i=>enter Z (s i) (v i))
local notation "P" i:max => spectator F (p i)
local notation "z" i:max => atPosition (o i) (r i) (x i)
local notation "z'" i:max => atPosition (o i) (s i) (y i)
local notation "Qₕ" i:max u:max => Q.packet h (z i) u (o i)
local notation "wage" => (fun i:J=> s i + (r i/s i)^(h+1))
local notation "wΩ" i:max d:max e:max => r i^(∑ j,d j)*s i^(∑ j,e j)

def testCentre {K:Type}[Fintype K]{e:K→ℕ} (h:ℕ) (p:Viewers F) (o:E4) (y:K→E4) (v: Labels S e) (r:ℝ) : Sec G h→ₗ[ℂ] ℂ :=
   (upon (spectator F p) h o y v).comp (frame Z r h).toLinearMap
lemma TC (i s) : testCentre F Z h (p i) (o i) (z' i) (V i) (r i) s=
    Orbits.whole (P i) (atPosition (o i) (r i) (fun (_:Unit)=>0)) (fun (_:Unit)=>frame Z (r i) h s) (z' i) (V i) := by
  rw [show atPosition (o i) (r i) (fun (_:Unit)=>0) = sole (o i) from funext fun j=>by simp [atPosition,sole]]; rfl
local notation "D" p:max i:max => testCentre F Z h (p i) (o i) (z' i) (V i) (r i)
omit [Fintype I] [Fintype K] in
include hx mn in
lemma central : ∀ᶠ i in l,Flash259HorizonFork.Ready (r i) (s i) M δ (fun (_:Unit)=> (0:E4)) (y i) := hx.mono fun i h=>
  ⟨h.length,h.adj,fun _=> by simpa using mn,h.reaches,h.away,fun a b h=>False.elim (h (Subsingleton.elim ..)),h.separated,h.gap⟩
include H hq hZ hQ hx hs mn dp hv
lemma center_phase (q:J→Viewers F) (b:Toon G h) : Allowance l r s (fun i=> (D p i) (theory b)-(D q i) (theory b)) := by
  simp_rw [ TC ]; exact split_phase F Z Q H hZ hq hQ hs mn dp (central mn hx) (q:=q) (o:=o) (u:=fun i => fun (_:Unit)=> theory b) (d:=fun _=>h) (fun _ c=>Allowance.fixed _) hv p
lemma center_budget (b:Toon G h) : Allowance l r (fun _=>1) (fun i=> (D p i) (theory b)) := by
  let T (i:J):=whole₁ (S:=S) (P i) (d:=fun (_:Unit)=>h) (e:=e) (sole (o i)) (z' i)
  let T' (i) (v:Labels S e) := sectionLabels (d:=Sum.elim (fun (_:Unit)=>h) e) v (moment (S:=S) (P i) (d:=Sum.elim (fun (_:Unit)=>h) e) (beside (sole (o i)) (z' i)))
  refine (together F Z H hZ hq hs (central mn hx) (d:=fun _=>h) (u:=fun (_:J) => fun (_:Unit)=> theory b) (hu:=fun _ c=>Allowance.fixed _)
    hv (fun _=>1) (fun i v => T i v) T' ?_ ?_).congr ?_
  · apply Eventually.of_forall; intro i u v; unfold T T'; rw [ ← whole₁_eq ]; exact Eq.symm (sectionLabels_apply ..)
  · intro d e' u l v w
    let h':=d (); have he : d=fun _=> h' :=funext fun _=>rfl
    -- can't subst h' deps, general `compact_pay` for d⊕e' (J geometry). receipts then Lite.
    have p := shorten hs hx (compact_pay F Q sim (Z 0) mn dp hQ.toSingleLog (d:= Sum.elim d e') (stages v w) hs (o:=o) (outer_scope mn dp hx) p)
    refine (p.transport (IsBigO.of_bound' ?_)).congr ?_
    · filter_upwards [hx] with i h; have e:=h.length.trans_le h.adj; have v:=h.length
      rw [Fintype.sum_sum_type,pow_zero,pow_add]; simp only [norm_div,norm_mul,norm_pow,norm_one, Real.norm_of_nonneg v.le, Real.norm_of_nonneg e.le]
      apply div_le_div_of_nonneg_left zero_le_one (by positivity) _; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ v.le h.adj _) (by positivity)
    filter_upwards [hx] with i h; unfold T;
    rw [ ← whole₁_eq ]; have hp:= center_profiles (o i) h dp; rw [lite F _ hp,far_lite F _ hp]; rfl
  refine Eventually.of_forall fun i=>?_ ; dsimp only; rw [ ←whole₁_eq]; rfl

include hu
lemma field_quote (b:Toon G h) : Allowance l r (fun _=>1) (fun i=> coord b ((frame Z (r i) h).symm (Q.packet h (z i) (U i) (o i)))) :=
  packet_size F Z Q H hZ hq hQ.toSingleLog (smaller_radius hs hx) u (fun i=> z i) o mn dp hu (near_scope hx) b

-- continuous package of true pricing, still functions since supports may be empty
lemma worth : Allowance l r (fun _=>1) (fun i=> Orbits.whole (P i) (z i) (U i) (z' i) (V i)) := by
  have hr:=smaller_radius hs hx
  let P0 i:= Orbits.whole (P i) (z i) (U i) (z' i) (V i)
  let R i:=testCentre F Z 0 (p i) (o i) (z' i) (V i) (r i)
  let A i := (frame Z (r i) 0).symm (Q.packet 0 (z i) (U i) (o i))
  have hh := paid_discrepancy F Z Q H hZ hq hQ hs mn dp hx hu hv p (h:=0) (o:=o)
  have H': Allowance l r (fun _=>1) (fun i=> R i (A i)) := by
    simp_rw [show ∀ i:J, R i (A i)=∑ j, R i (theory j)*numbers (A i) j from fun i=>beats ..]; refine Allowance.sum hr _ _ fun j _=>?_
    exact ((Allowance.mul (center_budget F Z Q H hZ hq hQ hs mn dp hx hv p j (o:=o)) (field_quote F Z Q H hZ hq hQ hs mn dp hx hu hv j (o:=o))).extend (Eventually.of_forall fun _=>one_mul _))
  -- no need to choose more than one h; method proof Pricing via G6 & c.
  refine (Allowance.add hr (hh.transport (IsBigO.of_bound 2 ?_)) H').congr ?_
  · have H : ∀ᶠ i in l,s i ≤ 1 := (tendsto_nhdsWithin_iff.mp hs).1.eventually (ge_mem_nhds zero_lt_one)
    filter_upwards [hx,H] with i h H; have p:=h.length.trans_le h.adj; have v:=h.length
    rw [pow_one,norm_one,mul_one,Real.norm_of_nonneg (by positivity)]; linarith only [H,(div_le_one p).mpr h.adj]
  refine Eventually.of_forall fun i=>?_ ; unfold discrepancy; dsimp only; unfold R testCentre; rw [LinearMap.comp_apply]; change _-_ + upon (P i) _ _ _ _ (frame Z _ 0 _) = _; unfold A; rw [LinearEquiv.apply_symm_apply,sub_add_cancel]
end YM.FVA2.GradedFar259.Original
