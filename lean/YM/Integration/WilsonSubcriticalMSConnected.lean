import YM.Integration.WilsonSubcriticalMSStationary
import YM.FVA2.Main

/-! Every connected row with two or more pure unit insertions vanishes in the actual
commissioned MS time-ordered field.  The independent bulk is the one fixed by MS_Data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalMSConnected
open Function Set Filter Finset MeasureTheory MS MS.Plane MS.Plane.Flux MS.Koszul MS.Landau
open MS.Arts MS.Land MS.Motif MS.Local.Physical MS.Rake MS.Rake.Geo MS.Latch MS.Latch.Job
open MS.Tone MS.Osc MS.Osc.Snap MS.Tide MS.Dial MS.Vane MS.Outlook MS.Menus
open WilsonSubcriticalRichOptics
open scoped Classical Topology BigOperators
variable {G:Gauge} {B:Deck G} {A:Booked B} {I W:Type} [LinearOrder W]

def amount (z:W→ℂ)(s:Finset W)(k:ℕ):ℂ:=if s.card=1 ∧ k=0 then ∑w∈s,z w else 0

def field (G:Gauge)(I:Type)(z:W→ℂ):Dance G I W:=fun s k _ _=>coin (amount z s k)

omit [LinearOrder W] in
private theorem omitted (z:W→ℂ)(s:Finset W)(h:s.card≠1):field G I z s=0:=by
  funext k i t w;change coin (amount z s k) w=0
  rw [amount,if_neg (fun e=>h e.1)];cases w <;> rfl

private theorem contact (K:Edge G)(μ:Measure QP)(r:QP)(a b:ℂ):Cabin r K μ (coin a) (coin b)=0:=by
  funext w;unfold Cabin
  rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_];exact map_zero (allocate ..)
  intro x y _;simp [meshZ,coin]

private theorem bulk_zero (K:Planet G I)(F:Glade G I):expJ K F 0=0:=by
  funext i t w;unfold expJ tree
  rw [scatter_congr _ _ _ (fun _ _=>(0:ℂ)) ?_];exact map_zero (allocate ..)
  intro x y _;simp [attaches]

omit [LinearOrder W] in
private theorem crossed (μ:I→Measure QP)(K:Planet G I)(x:I→QP)(z:W→ℂ)(s t:Finset W)(k n:ℕ):
    regionC μ x K (field G I z s k) (field G I z t n)=0:=by
  funext i y;exact contact (K i y) (μ i) (x i) _ _

theorem prescribed (P:Geo I)(M:MS_Data G A)(j:W→Plaid B 0)(x:Position W I):
    DOrd A P M (fun w=>⟨0,j w⟩) x (field G I (fun w=>valueAtUnit (j w))):=by
  let z:=fun w=>valueAtUnit (j w)
  refine ⟨omitted z ∅ (by simp),?_ ,?_⟩
  · intro w;funext k i t
    change coin (amount z {w} k)=Archive 0 (M.marks 0 (j w)) k (P.η i,t)
    rw [WilsonSubcriticalMSStationary.archived A (j w) M k t (P.η i)]
    simp [amount,z,WilsonSubcriticalMSStationary.scalar]
  · intro s hs k
    have h:s.card≠1:=by omega
    have zeroS:=omitted (G:=G) (I:=I) z s h
    change Trip _ (field G I z s k) (multi _ _ _ _ _ (field G I z s) (field G I z) k s)
    rw [zeroS];unfold multi lonely
    simp only [Pi.zero_apply,bulk_zero,crossed,Finset.sum_const_zero,add_zero]
    refine ⟨collect_z,?_,?_⟩ <;> rw [(retire _ _).empty,add_zero]
    · intro i t l _;exact integrableOn_zero
    · exact river0.symm

theorem book (M:MS_Data G A)(j:W→Plaid B 0)(u:ℝ){x:W→QP}(sep:Injective x)(s:Finset W)(k:ℕ):
    Dial.book M (fun w=>⟨0,j w⟩) u x s k=amount (fun w=>valueAtUnit (j w)) s k:=by
  have he:=Rake.perfect (pin M (fun w=>⟨0,j w⟩) u sep) (prescribed (frameF Unit u) M j (fun w _=>x w))
  unfold Dial.book;rw [he];change limUnder atTop (fun _:ℝ=>amount (fun w=>valueAtUnit (j w)) s k)=_
  exact tendsto_const_nhds.limUnder_eq

end YM.Integration.WilsonSubcriticalMSConnected
