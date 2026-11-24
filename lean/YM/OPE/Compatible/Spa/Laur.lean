import YM.OPE.Compatible.Spa.Nacre
/-!
# The kernel of a filtered reading modulo the next flag

Under the compatibility, cutoff, and lifting hypotheses, `BayFin` writes a family
with zero `ReadK` as a controlled family in the next flag plus a remainder in
`Sapling`, preserving the specified phase trimming of the remainder. `Reef` identifies
the kernel on a single flag with membership in the sum of the next flag and `Sapling`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
private lemma subtractLift {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S A : I → Submodule ℝ E) (x p : ∀ i, S i) {w b : I → ℝ} (hw : 1 ≤ w) (hb : 0 ≤ b)
    (hx : Wealth (fun i => (x i).val) w b) (hp : Wealth (fun i => (p i).val) w b)
    (deep : ∀ i, (x i - p i).val ∈ A i) (Q : I → E → Prop) (admit : ∀ i, Q i (p i).val) :
    ∃ y : ∀ i, A i, Wealth (fun i => (y i).val) w b ∧ ∀ i, Q i ((x i).val - (y i).val) := by
  let y : ∀ i, A i := fun i => ⟨(x i - p i).val, deep i⟩
  refine ⟨y, subW hw hb hx hp, fun i => ?_⟩
  change Q i ((x i).val - ((x i).val - (p i).val))
  rw [sub_sub_cancel]
  exact admit i

private lemma differenceInNext (U : Z.Ω M Y) (e : J!) (i : M)
    (v w : U.flag e.val i)
    (pair : U.read e.val e.isLt i w = U.read e.val e.isLt i v) :
    (v - w).val ∈ U.flag (e.val + 1) i :=
  (U.depth e.val i e.isLt (v - w)).2 (stepDiff (G := Mint Z e.val) (U.read e.val e.isLt i) w v pair)

private lemma gradedLift {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (U : Z.Ω M Y) (hX : ∀ i, (V i).clip = p')
    (T' : Z.Floss V U hp (le_trans zero_le_one hq) k Hp a) (C : Bals Hp Z a A' κ)
    (hx : l*l ≤ τ 0) (X' : Lance X) (e : J!) (f : I → M) (b : I → ℝ) (hb : 0 ≤ b)
    (x : (i : I) → U.flag e.val (f i)) (h : Wealth (fun i => (x i).val) (Y ∘ f) b)
    (zero : ∀ i, ReadK Z κ U e (f i) (x i) = 0) (t : Phase)
    (trim : ∀ i, trims t.val (U.read e.val e.isLt (f i) (x i)).val) :
    ∃ p : (i : I) → U.flag e.val (f i), Wealth (fun i => (p i).val) (Y ∘ f) b ∧
      ∀ i, (p i).val ∈ Sγ (f i) ∧ U.read e.val e.isLt (f i) (p i) =
        U.read e.val e.isLt (f i) (x i) ∧ trims t.val (p i).val := by
  let v (i : I) := U.read e.val e.isLt (f i) (x i)
  have inside (i : I) : v i ∈ Dross Hp Z a e.val := ((C.tricks e).hero _).2 (zero i)
  exact harvestZ (Z := Z) (hq := (fun i => hq (f i) : 1 ≤ Y ∘ f)) (L := X')
    (a := a) (T' := Floss.pullAlong Hp T' f) (Hp := Hp) hx (fun i => hX (f i))
    e.isLt hb v inside ((U.branch f).bulk e.isLt x h) t trim

lemma BayFin {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(hX:∀ j,(V j).clip=p')(T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(C:Bals Hp Z a A' κ)(hx:l*l≤τ 0)(X':Lance X)(e:J!)(f:I→M)(b:I→ℝ)(hb:0 ≤ b)(x:(i:I)→ U.flag e.val (f i))(h:Wealth (fun i=>(x i).val) (Y∘f) b)(he:∀ i,ReadK Z κ U e (f i) (x i)=0) (t:Phase) (hs':∀ i,trims t.val (U.read e.val e.isLt (f i) (x i)).val):∃ y:(i:I)→U.flag (e.val+1) (f i),Wealth (fun i=>(y i).val) (Y∘f) b∧∀ i,(x i).val-(y i).val∈ Sγ (f i)∧trims t.val ((x i).val-(y i).val) := by
  obtain ⟨p, pay, props⟩ := gradedLift (hq := hq) Hp Z a U hX T' C hx X' e f b hb x h he t hs'
  exact subtractLift (fun i => U.flag e.val (f i)) (fun i => U.flag (e.val + 1) (f i))
    x p (fun i => hq (f i) : 1 ≤ Y ∘ f) hb h pay
    (fun i => differenceInNext Z U e (f i) (x i) (p i) (props i).2.1)
    (fun i v => v ∈ Sγ (f i) ∧ trims t.val v) (fun i => ⟨(props i).1, (props i).2.2⟩)

set_option maxHeartbeats 200000 in
lemma Reef {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(hX:∀ j,(V j).clip=p')(T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(C:Bals Hp Z a A' κ)(hx:l*l≤τ 0)(X':Lance X)(e:J!)(v:M)(x:U.flag e.val v) : ReadK Z κ U e v x=0 ↔ x.val∈ Bay U.flag (Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)) (e.val+1) v:=by
      refine ⟨fun h=>?_, deepRun (hq:=hq) Hp Z a C U T' e v x⟩; obtain ⟨q,hH,hQ⟩:= BayFin (hq:=hq) Hp Z a U hX T' C hx X' e (fun _:Unit=>v) 1 zero_le_one (fun _=>x) (wealthC _) (fun _=>h) 0 (fun _=>trims.be _); exact Submodule.mem_sup.mpr ⟨(q ()).val,(q ()).property,_,(hQ ()).1,add_sub_cancel (q ()).val x.val⟩ 
end YM.OPE.Stroke
