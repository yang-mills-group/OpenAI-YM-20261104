import YM.Integration.WilsonAddressedPublicNamedQuadrature
import YM.Integration.WilsonMeasuredPublicEntrancePublicFour
import YM.Integration.WilsonMeasuredPublicEntranceSmoothWeights

/-! Take the selected physical limit of the same reflected Wilson measurements and of their cutoff-dependent projected fields. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonMeasuredPublicEntranceSmoothPublic
open Function Filter Finset Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonAddressedPublicSelfPurchase (source)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "caps" => grades (d 0).val (d 1).val


open WilsonMeasuredPublicEntrancePublicFour (sign)
open WilsonMeasuredPublicEntranceCoverCells (mass)
open WilsonMeasuredPublicEntranceSmoothWeights
open WilsonAddressedPublicNamedQuadrature (value)
variable (ax:Axis)(site:ℕ){n:ℕ}(φ:Test n)(a scale:ℝ)(pin:(Fin n→ Cover)→Fin 2→ Cover)

def observed (w:ℕ×ℕ)(o:Fin 2→ Cover):ℂ:=
  ∑b,sign b*physical caps site o w.1 w.2 (source R F B d (fun i=>v i (b i)) b ax w)
def running (w:ℕ×ℕ)(o:Fin 2→ Cover):ℂ:=
  ∑b,sign b*publicValue (S:=S) caps site o (source R F B d (fun i=>v i (b i)) b ax w)
def named (o:Fin 2→ Cover):ℂ:=
  ∑b,sign b*value R F d (fun i=>v i (b i)) ax site o

theorem reported (pos:0<a)(below:(l:Filter (ℕ×ℕ))≤f.fuse)
    (safe:∀o,mass φ a scale o≠0→Extraction.Order.grid (C) site (pin o)∈YM.generic 2):
    Tendsto (fun w:ℕ×ℕ=>φ.applyTo (fun x=>observed R F B d v ax site w (pin (address a (scale • x)))))
      (l:Filter (ℕ×ℕ)) (𝓝 (φ.applyTo (fun x=>named R F d v ax site (pin (address a (scale • x)))))):=by
  classical
  apply limit φ a scale pos (fun w o=>observed R F B d v ax site w (pin o)) (fun o=>named R F d v ax site (pin o))
  intro o occupied
  apply tendsto_finsetSum
  intro b _
  apply Tendsto.const_mul
  simpa only [Fintype.sum_unique,one_mul] using WilsonAddressedPublicNamedQuadrature.physical_limit
    R F B d (fun i=>v i (b i)) b ax site (fun _:Unit=>pin o) (fun _=>1) below (fun _=>safe o occupied)

theorem ordered (pos:0<a)(safe:∀o,mass φ a scale o≠0→Extraction.Order.grid (C) site (pin o)∈YM.generic 2):
    Tendsto (fun w:ℕ×ℕ=>φ.applyTo (fun x=>observed R F B d v ax site w (pin (address a (scale • x))))-
      φ.applyTo (fun x=>running R F B d v ax site w (pin (address a (scale • x))))) f.fuse (𝓝 0):=by
  classical
  have live:∀ᶠ w:ℕ×ℕ in f.fuse,site≤w.1:=by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  have single(o)(occupied:mass φ a scale o≠0)(b:Fin 2→Bool):
      Tendsto (fun w:ℕ×ℕ=>let Y:=source R F B d (fun i=>v i (b i)) b ax w
        physical caps site (pin o) w.1 w.2 Y-publicValue (S:=S) caps site (pin o) Y) f.fuse (𝓝 0):=by
    rw [Metric.tendsto_nhds]
    intro ε ep
    filter_upwards [live,WilsonAddressedPublicOrderedQuadrature.original R F B d v site
      (fun _:Unit=>pin o) (fun _=>safe o occupied) (half_pos ep)] with w late sale
    have h:=sale ax b (fun _:Unit=>1) late
    simp only [Fintype.sum_unique,one_mul,norm_one,WilsonAddressedPublicOrderedQuadrature.at_grid R d late] at h
    rw [dist_zero_right];exact lt_of_le_of_lt h (half_lt_self ep)
  let H:=fun w o=>observed R F B d v ax site w (pin o)
  let U:=fun w o=>running R F B d v ax site w (pin o)
  have cell(o)(occupied:mass φ a scale o≠0):Tendsto (fun w=>H w o-U w o) f.fuse (𝓝 0):=by
    have h:=tendsto_finsetSum Finset.univ (fun b _=>(single o occupied b).const_mul (sign b))
    simpa only [H,U,observed,running,mul_sub,Finset.sum_sub_distrib,mul_zero,Finset.sum_const_zero] using h
  have total:=limit φ a scale pos (fun w o=>H w o-U w o) (fun _=>0) cell
  have zero:φ.applyTo (fun _:Points n=>(0:ℂ))=0:=by
    simp [Test.applyTo]
  rw [zero] at total
  change Tendsto (fun w=>φ.applyTo (fun x=>H w (address a (scale • x)))-φ.applyTo (fun x=>U w (address a (scale • x)))) f.fuse (𝓝 0)
  simp_rw [WilsonMeasuredPublicEntranceSmoothWeights.sub φ a scale pos H U]
  exact total

end YM.Integration.WilsonMeasuredPublicEntranceSmoothPublic
end
