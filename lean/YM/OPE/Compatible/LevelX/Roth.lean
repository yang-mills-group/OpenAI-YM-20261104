import YM.OPE.Compatible.LevelX.Lot
import YM.OPE.Compatible.Grotto.Tin
/-!
# Ball top mean eta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
open Hark
variable (d)
-- Length flags choose T and gaps. get contract and uniform.Aware.
noncomputable def lapPrice (S:Side)(i:ℕ) :ℝ:= (S.val:ℝ)⁻¹^i
def EndPrice (D:ℕ)(S:Side):ℝ:= lapPrice S D /4
lemma EndFare (L:Side)(x:ℕ):0 < lapPrice L x:=by unfold lapPrice; positivity
lemma stairPrice (L:Side)(i j:ℕ)(h:i<j)(hp:3 ≤ L.val): lapPrice L j < lapPrice L i:=by
    apply pow_lt_pow_right_of_lt_one₀ (by positivity) _ h; apply inv_lt_one_of_one_lt₀; exact_mod_cast (show 1 < L.val by omega)
lemma arrival (L:Side)(i j:ℕ)(h:i≤ j)(hp:3 ≤ L.val):EndPrice j L< lapPrice L i:=by
    calc _ < lapPrice L j:=by unfold EndPrice; have ht:= EndFare L j; linarith
         _ ≤ _:=by obtain h|rfl:=Nat.lt_or_eq_of_le h; exact (stairPrice L _ _ h hp |>.le)
                   rfl
-- Sect norms
lemma rift (v:ℕ) : FiniteDimensional ℝ (Bead G d v):=by infer_instance
lemma pullG (G:Gauge)(s D k m i:ℕ)(h:D<m)(he:D≤k)(ht:i<D+1): ∃ X:Bead G s i→L[ℝ] fillet G k m i (by omega),∀ x,stepRead G s i k m (by omega) (X x).val=x:=by
     haveI Q:= rift (G:=G) s i; let B:= fillet G k m i (by omega); let P:= stepRead G s i k m (by omega)∘L B.subtypeL; have hx: Surjective P.toLinearMap:=by intro v;obtain ⟨p,hp,hT⟩:= obtains (G:=G) s (e:=i) (m:=m) (k:=k) (by omega) (by omega) v; exact ⟨⟨p,hp⟩,hT⟩
     obtain ⟨u,hu⟩:= P.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hx); let X:Bead G s i →L[ℝ] B:={ u with cont:= (show Continuous u from by exact LinearMap.continuous_of_finiteDimensional (𝕜:=ℝ) (E:=Bead G s i) (F':=↥B) u) }; exact ⟨X, fun x=>LinearMap.congr_fun hu x⟩
-- fixed choices. for all μ
noncomputable def tuneG (G:Gauge)(D k m:ℕ)(h:D<m)(he:D≤k)(u:ℝ)(L:Side)(hp:3≤ L.val):Cuts (D+1) (lapPrice L) (EndPrice D L) u (bed G k m) (Bead G D) where
     flag i:= fillet G k m (min i (D+1)) (by omega)
     Tap i:= if ht:i<D+1 then stepRead G D i k m (by omega) else 0
     first:=dawn
     next i hx p:=by simp_rw [Nat.min_eq_left (show i+1≤D+1 by omega), Nat.min_eq_left (show i≤D+1 by omega),dif_pos hx]; constructor; intro hx'; have hp:p∈fillet G k m i (by omega):=prev p (by omega) hx'; exact ⟨hp,(slogan (by omega) (d:=D) (by omega) p hp).mpr hx'⟩; rintro ⟨hp,hP⟩; exact (slogan (by omega) (by omega) p hp).mp hP
     closed:= by simp only [min_self]; apply downSector (d:=D) h le_rfl
     lift i hx:= (fillet G k m i (by omega)).subtypeL ∘L (pullG G D D k m i h he hx).choose
     rises i hx v:=by simp only [min_eq_left hx.le,dif_pos hx]; exact ⟨((pullG G D D k m i h he hx).choose v).property,(pullG G D D k m i h he hx).choose_spec v⟩
     tempo i _:= EndFare ..
     fast:= div_nonneg (EndFare ..|>.le) (by norm_num)
     finishes _ hx:= arrival _ _ _ (Nat.le_of_lt_succ hx) hp
     beats _ _ hx _:= stairPrice L _ _ hx hp
end YM.OPE.Drift
