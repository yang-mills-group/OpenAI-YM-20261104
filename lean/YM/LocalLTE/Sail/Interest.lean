import YM.LocalLTE.Sail.Bills
import YM.LocalLTE.Sail.Wrap
import YM.LocalLTE.Sail.PaidBoot
/-!
# Purchase after the opportunity, uniform in all actual heights
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}
open Pressure ConnectedActivityE6 Bandage.Harmonics Motion
variable (G) (l p q N K :ℕ) (a ε :ℝ) (s: Stage)
open Doors LocalLTE.Port
/-- Need both #support and #budget-covers, and stencil may also move. -/
def marksVolume :ℕ:=1+∑ i∈ Finset.range (p+1), (localSection G i).stencil.card
def marksExpense (x:ℝ):ℝ:= ∑ i ∈ Finset.range (p+1),zoneFee G i x
lemma volume_ge (i)(hi:i≤p) : (localSection G i).stencil.card ≤ marksVolume G p:=by
    unfold marksVolume; exact (Finset.single_le_sum (f:=fun i=>(localSection G i).stencil.card) (fun i _=>Nat.zero_le _) (show i∈ Finset.range (p+1) from Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans (Nat.le_add_left ..)
lemma expense_ge (i x) (hi:i≤p)(hp:0≤x): zoneFee G i x≤ marksExpense G p x:= Finset.single_le_sum (f:=fun i=>zoneFee G i x) (fun i _=> mul_nonneg (zero_le_one.trans (Doors.cameras_ge G i)) (pow_nonneg hp _)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
private noncomputable def priceStart (e t:ℝ):= birthFee (Doors.stain t) (marksExpense G p t) e K (marksVolume G p)
-- e:A per-index exponent. v needed can be extremely small. Real.
lemma employed (v:ℝ) : ∀ᶠ t:ℝ in atTop,birthFee (Doors.stain t) (marksExpense G p t) a K (marksVolume G p) ≤ t^v* Urns.divisor t:=by
    let V(t:ℝ) := 1+Real.exp (a*marksVolume G p) * marksExpense G p t
    let W:=(K:ℝ)*(marksVolume G p)+1; have hW:0≤W:=by unfold W; positivity
    have ht : ∃ n:ℕ,Rate G oneQ n V:=by
       let hz(i):=Extra.Histories.degree ((Labels.frames G).level i); -- ht name
       let s:= Finset.range (p+1); have hz': Rate G oneQ 1 (fun x:ℝ=>x):=by simpa only [oneShift,Real.rpow_one] using! (Rate.power (G:=G) (L:=oneQ) (a:=(1:ℝ))) -- untyped i
       have hV(i): Rate G oneQ (hz i:ℝ) (fun t=> zoneFee G i t):= by unfold zoneFee; simpa only [one_mul] using! ( (hz'.pow (hz i)).mul_left (Doors.cameras G i))
       have hp(U:Finset ℕ):∃ u:ℕ,Rate G oneQ u (fun t=>∑ i∈U,zoneFee G i t):=by
           induction U using Finset.induction with
           | empty=> exact ⟨0,(by simp only [Nat.cast_zero,Finset.sum_empty]; exact Rate.const _)⟩
           | insert i U hi ih=> obtain ⟨n,h⟩:=ih; refine ⟨hz i+n,?_⟩; simp only [Finset.sum_insert hi]; exact Rate.add ((hV i).weaken (Nat.cast_le.mpr (Nat.le_add_right ..))) (h.weaken (Nat.cast_le.mpr (Nat.le_add_left ..)))
       obtain ⟨n,hN⟩:=hp s; exact ⟨n,((Rate.const _).weaken (Nat.cast_nonneg _)).add (hN.mul_left _)⟩
    obtain ⟨n,hN⟩:= ht; let d:ℝ:= n*K; have hv : Rate G oneQ d (fun x=> V x^K):= hN.pow K
    let f x:= ((W*Real.exp W)*Urns.divisor x)*(V x^K); have hF: Rate G oneQ (v-1) f:=by convert! (((Mallow.cheapest (G:=G) oneQ (v-d-1)).mul_left _).mul hv) using 1; ring -- orientation
    filter_upwards [eventually_ge_atTop (1:ℝ),hF v (by linarith only)] with x hx h
    rw [oneShift] at h
    let c:= Doors.stain x; have hc:0<c:= stain_pos x
    have hKf : Real.exp (W*c)-1 ≤ W*c*Real.exp W:= (exp_difference _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_of_le_one_right hW (stain_le x))) (mul_nonneg hW hc.le))
    have hu:0≤ V x := by unfold V; have hz:0≤ marksExpense G p x:= Finset.sum_nonneg fun i _=>mul_nonneg (zero_le_one.trans (Doors.cameras_ge G i)) (pow_nonneg (zero_le_one.trans hx) _); positivity
    let ψ:= Urns.divisor x; have hZ : ψ^2=c:= by exact Real.sq_sqrt hc.le
    unfold birthFee; refine (mul_le_mul_of_nonneg_right hKf (pow_nonneg hu K)).trans (le_trans ?_ (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (Urns.nonzero x|>.le)))
    change W*c*Real.exp W * (V x^K) ≤ f x * ψ; rw [← hZ]; change W*ψ^2*_ *_ ≤ (W* _ *ψ)* _ * ψ; exact le_of_eq (by ring)
end YM.PhysicalNext.Repeat.Legato.Spiral
