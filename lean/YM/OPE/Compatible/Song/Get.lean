import YM.OPE.Compatible.Song.Heed
/-!
# Material operations.Phase-wise.No infinite-series semantics
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL
variable {i j d k m r l b:ℕ}{n:Side}
variable {I W:Type}
variable {N:I→ Side}{φ:Filter I}{Z:I→ℝ}
variable {M:I→ℕ}(A:Audience φ Z N M r)
structure EarthX (B:I→Finset (Edge Cover))(φ:Filter I)(Z:I→ℝ)(p:Forge G N)(d:ℕ):Prop where
       pay : PlaneQ B φ Z p d
       mass: Divining φ p
variable (ht:Tendsto Z φ atTop)
variable {B:I→Finset (Edge Cover)} {P Y:Forge G N}
namespace EarthX
include ht
lemma below (s:Phase)(p:EarthX B φ Z P k)(hv:k≤d+s.val):EarthX B φ Z (LiftA s P) d:= ⟨PlaneQ.zoomP ht s p.pay hv,vpFan s p.mass⟩
lemma birth0: EarthX B φ Z (0:Forge G N) d:=⟨PlaneQ.empty ht,Divining.zeroP⟩
lemma shift (h:EarthX B φ Z P d)(hv:EarthX B φ Z Y d):EarthX B φ Z (P-Y) d:=⟨PlaneQ.shiftz ht h.pay hv.pay,h.mass.subB hv.mass⟩
lemma height (h:EarthX B φ Z P d)(hv:EarthX B φ Z Y d):EarthX B φ Z (P+Y) d:=⟨PlaneQ.Shade ht h.pay hv.pay,h.mass.sumB hv.mass⟩
lemma march (S:Finset W)(p:W→Forge G N)(h:∀ i∈S,EarthX B φ Z (p i) d):EarthX B φ Z (∑ i∈S,p i) d:=by
       induction S using Finset.induction_on with
       | empty=> rw[sum_empty]; exact birth0 ht
       | insert i s hi ih=> rw [sum_insert hi]; exact height ht (h _ (mem_insert_self ..)) (ih (fun _ h'=> h _ (mem_insert_of_mem h')))
omit ht
lemma further {S:I→Finset (Edge Cover)}(h:EarthX B φ Z P d)(hv:∀ i,B i⊆ S i): EarthX S φ Z P d:=⟨⟨fun i=> (h.pay.roll i).wider hv⟩, h.mass ⟩
end EarthX
noncomputable def gapV (p:Forge G N)(n:ℕ) (φ:Filter I):=∀ j:Phase,j.val < n→ ∀ᶠ i in φ,eyeR p j i=0
lemma hushed {p: Forge G N} (q:Phase)(h:gapV p q.val φ)(hv:Divining φ p):∀ᶠ i in φ,LevelA (tor (N i)) (eyeR p q i):=by
       filter_upwards [hv.he,eventually_all.mpr (fun i:Phase=>show ∀ᶠ j in φ,i.val<q.val→eyeR p i j=0 from by by_cases ht:i.val<q.val; exact (h i ht).mono (fun i hi _=>hi); exact Eventually.of_forall fun i hi=>False.elim (ht hi))] with i hi he; exact LinearBell _ hi q fun j hj x=> congr_fun (he _ hj) _
noncomputable abbrev FixP (B:I→Finset (Edge Cover))(φ:Filter I)(Z:I→ℝ)(P:Forge G N)(d:ℕ)(s:Phase)(k:ℕ):Prop:= EarthX B φ Z P d ∧ gapV P s.val φ ∧ Filμ B φ Z (eyeR P s) k
lemma eye_sub (p q:Forge G N)(r:Phase):eyeR (p-q) r=eyeR p r-eyeR q r:=by fin_cases r <;> rfl
lemma eye_add (p q:Forge G N)(r:Phase):eyeR (p+q) r=eyeR p r+eyeR q r:=by fin_cases r <;> rfl
noncomputable def PathW (p:Forge G N)(q:Phase): GlyphQ G N:=eyeR p q
lemma eye_sum (p:W→Forge G N) (q:Finset W)(s:Phase):eyeR (∑ i∈q,p i) s=∑ i∈q,eyeR (p i) s:=by induction q using Finset.induction_on with
                                                                                                         | empty=>rw[sum_empty,sum_empty]; fin_cases s<;>rfl
                                                                                                         | insert _ _ h ih=> rw[sum_insert h,sum_insert h,eye_add, ih]
lemma lowerV {p:GlyphQ G N} (hv:Filμ B φ Z p (k+1))(h:∀ᶠ i in φ,Claw.rank (p i) (k+1)=0): Filμ B φ Z p k:=⟨hv.here,(hv.tariff.and h).mono (fun i hi=>by simpa using (Tall.dropT hi.1 hi.2)),hv.loud⟩
end YM.OPE.Merchant
