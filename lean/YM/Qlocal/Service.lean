import YM.Qlocal.Reclosure
import YM.Qlocal.Printed

/-! Combined books. This is actual pre model (not identified Fk),
native layout preserving density under real reclosure. Marks at all independent
test points chosen simultaneously (even zeros), pre-engineering currencies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Service
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}
open Merge Switch UniformPays Publishing

variable {Z:ι→Poly R} {e:ι→ Support n} (h:Syntax Z s e) (hO:∀ i,o i∈s i)
    [Fintype ι] {K:WayK Ω ι G n} {L:Ω→J→ Config G n → Ways ι}
    (Y : Spectrum Ω ι G n J) (hr: Y.Reads P.p L)(hx:Y.Costs P.p e a A)(hK : UniformPays P.activities P.p K B d)
    (he: ∀ x i u,u∈e i→ Motion.Hush i u (fun j=> (P.activities.forced j).support) (K x))

local notation "S'"=> script Z K Y
include hr
lemma painted (U:Config G n)(x:Ω)(i:J) : (S').painted P x U i = Switch.sound Z (L x i U):= by
 rw [← Y.service P.p R Z hr]; unfold Ledger.painted Spectrum.polled -- order error ?
 split
 next hy => unfold Spectrum.paint; rw [if_pos (show Y.total i from hy)]; rfl
 next hl => unfold Spectrum.paint; rw [if_neg (show ¬Y.total i from hl)]; by_cases ht:Healthy P.p.threshold (Y.region i) U
            · rw [masked_eq _ _ _ _ (show Healthy P.p.threshold ((S').region i) U from ht),masked_eq _ _ _ _ ht]; rfl
            rw [masked_ne _ _ _ _ (show ¬ Healthy P.p.threshold ((S').region i) U from ht),masked_ne _ _ _ _ ht, Complex.ofReal_zero,zero_smul]

variable {f' : Side} {P' : RG.Rep G f'} {S: StepData n f'}
    {T: Pressure.Tube G S} {Q : Pressure.Teller G} {Q₀:ConnectedActivityE6.Target G Q}
    {W β μ z :ℝ} {δ₀:Side} {O: ConnectedActivityE6.Target.Order G W}
    (D:ConnectedActivityE6.Cash W β μ δ₀ Q₀ O z T P')
    {M:Ω→ι→Lotus.Leaf P'} {g:ι→ℝ} (hσ:SwitchStep M S g (Real.exp ∘ P.exponent) P.activities P.p K L)
    (hp:P.p.supportExponent ≤ d)
    (X':J→ℝ) (hX':Summable X')(hp':∀ x i,Paid (fun U=> L x i U) (X' i))
include h he hp' hX' hK hp hσ hx hO
set_option quotPrecheck false
local notation "A'"=> (S').taste P o s
set_option quotPrecheck false
variable [Countable J] [Nonempty V] [Fintype V]
set_option maxHeartbeats 500000
include D
lemma answers (x:Ω) (U:Config G n):
    S.push P'.beta (Photo.given (S:=S) (M x) g R Z) U = (((A').leaf x).density) U := by
  have hV:= weighs P h hO Y hr hx hK he; have hv(i): Paid (fun _ : Unit=> L x i U) (X' i):= Paid.toPoint _ (hp' x i) _
  have he := hσ.full D hK hp R Z h.repeated h.proper U X' (fun x i=>Paid.toPoint _ (hp' x i) _) hX' x;
  have hSr: Summable (fun i=>sound Z (L x i U)):= (Switch.soundSum Z (fun i=> L x i U) hv hX' (F:=fun u t=>∑' i,L x i U u t) (fun x _ i=>rfl)).summable
  rw [he]; unfold RG3.Forms.Deck.density;
  let φ := (S'); let Φ:= A'; have hΓ i: φ.painted P x U i = _:= painted Y hr U x i -- binder fix
  have hL': (Φ.leaf x).log U=∑' j : J,sound Z (L x j U):= by
    rw [Ledger.log_sum _ _ _ _ _ _ (hSr.congr (fun i=>(hΓ i).symm)) (fun i=>hV.constant x i U) ?_ ?_]; exact tsum_congr hΓ
    · intro j hj; by_cases ht:(S').total j.1
      · rw [Ledger.painted, if_pos ht]; exact Classical.byContradiction (fun hl=> hj (hV.owns x j.1 j.2.val U hl))
      unfold Ledger.painted; rw [if_neg ht]; by_cases hx:Healthy P.p.threshold (S'|>.region j.1) U; rw [masked_eq _ _ _ _ hx]; exact Classical.byContradiction (fun hl=> hj (hV.owns x j.1 j.2.val U hl)); rw [masked_ne _ _ _ _ hx,Poly.part_nil]
    intro j; by_cases ht:(S').total j
    · rw [Ledger.painted, if_pos ht]; exact hV.quiet x j U
    unfold Ledger.painted; rw [if_neg ht]; by_cases hx:Healthy P.p.threshold (S'|>.region j) U; rw [masked_eq _ _ _ _ hx]; exact hV.quiet x j U; rw [masked_ne _ _ _ _ hx,Poly.part_nil]
  dsimp only [Function.comp_apply]; have hy:= (S').forced_cluster P o s x U (fun i=> hV.base x i U); have he':((((A').leaf x).contents).cluster U)=∑' p,Photo.fronts P.activities (fun i => (S').forced x i U) U P.p p:= hy
  rw [show ( (A').leaf x).log U=_ from hL',he']; rfl

end YM.Qlocal.Service
