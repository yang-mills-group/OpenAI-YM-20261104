import YM.GradedFar.Round.Scene

/-!
# Rates for `Y^0` and its actual phase discrepancy
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books
open Scale Dframe
open OPE Orbits Logged OPE.Logged.Deck Horizon
open Logged.Economy (Paint)
open OPE.Log (badge)
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t : ℕ} {I:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K) (hl: LogTrace U Q.port)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "Φ"=>spectator U
variable (D : Deck.Pitch I) (u:I→Inputs G d)(v:I→Inputs G e)
lemma far_positions (r s:ℝ)(o:E4) (y:Points m)(hr:0<r) : atPos r o ((s/r)•y)= atPos s o y := by
  funext i; change o+(r • ((s/r) • y i))=_; rw [smul_smul, mul_div_cancel₀ _ hr.ne']; rfl -- mul_div_cancel₀ side
lemma landed_slots (r s:ℝ) {M δ:ℝ} {x:Points n} {y:Points m} (hc:Terracing r s M δ x y) (hd:0<δ) :
     r • forest x ((s/r)•y) ∈ conf (n+m) := by
   have hp:= OPE.Logged.Fork.unique_part (show Fork.Landed r s M δ x.ofLp y.ofLp from ⟨hc.1,hc.2,hc.xcap,hc.ycap,hc.ynear,hc.xsep,hc.ysep,hc.together⟩) 0 hd
   change Injective (beside (atPos r 0 x) (atPos s 0 y)) at hp
   rw [← far_positions r s _ _ hc.pos] at hp; let z:= forest x ((s/r)•y)
   have hh : atPos r 0 z ∘ finSumFinEquiv=beside (atPos r 0 x) (atPos r 0 ((s/r)•y)):= by funext i; rcases i with i|i <;> simp [atPos,z,forest,points]
   rw [←hh] at hp; rw [show atPos r 0 z=(r • z).ofLp from funext fun i=> zero_add _] at hp
   intro i j h
   obtain ⟨a,rfl⟩:= (finSumFinEquiv : Fin n⊕ Fin m≃ Fin (n+m)).surjective i; obtain ⟨b,rfl⟩:= (finSumFinEquiv : Fin n⊕ Fin m≃ Fin (n+m)).surjective j; exact congrArg finSumFinEquiv (hp (show ((r • z).ofLp ∘ finSumFinEquiv) a = _ from h))

include H hq he
lemma accrued (P: Economy.Small I) (d j:ℕ) : Paint P (fun s=> P.r s^j) (fun s=> extracted U Q K d j (P.r s)) := by
    obtain ⟨k,C,hc,hA⟩:= brought N M H U Q J K θ hq he d j
    apply Paint.from_cost C hc k; filter_upwards [P.leaps.eventually hA] with i hi; rw [log_cost]; apply hi.trans_eq; ring
lemma grace (D:Economy.Small I)
    (h:∀ i,Paint D (fun _=>1) (fun s=> chair G (d i) (u s i))) :
    Synthesis.Samples U Q D D.r d (fun s=>here K (D.r s) (u s)) := by
    intro i j hj
    simpa only [mul_one,here] using Paint.times_cost (accrued N M H U Q J K θ hq he D (d i) j) (h i) (Eventually.of_forall fun l=>
      (show ‖Q.cutTest j (d i) (K (D.r l) (d i) (u l i))‖ ≤ _ from (by rw [← mapK_apply]; exact ContinuousLinearMap.le_opNorm (extracted U Q K (d i) j (D.r l)) _)))
section
variable (o:I→View U) {M' δ:ℝ}(hm:0≤M')(hd:0<δ)(x:I→Points n)(y:I→Points m)
    (hx:∀ᶠ i in D.p,Terracing (D.r i) (D.s i) M' δ (x i) (y i))
variable (hu:∀ i,Paint D.toSmall (fun _=>1) (fun s=> chair G (d i) (u s i)))
  (hv:∀ i,Paint D.toSmall (fun _=>1) (fun s=> chair G (e i) (v s i)))
include H hq he hl hm hd hx hu hv

def honest (r s:ℝ) (i:View U)(x: Points n) (y : Points m)(u:Inputs G d)(v:Inputs G e) :=
    Orbits.whole (Φ i.1) (atPos r i.2 x) (here K r u) (atPos s i.2 y) (here K r v)
set_option quotPrecheck false
local notation "ρ"=>D.r
local notation "σ"=>D.s
local notation "S"=> D.toSmall
local notation "Yγ"=>fun i q=> honest U K (D.r i) (D.s i) q (x i) (y i) (u i) (v i)
open private well_pitched from YM.GradedFar.Physical.Contours
lemma balance : Paint S σ (fun i=> Yγ i (o i)-Yγ i (none,(o i).2)) ∧ Paint S (fun _=>1) (fun i=> Yγ i (o i)) := by
   have ht:=grace N M H U Q J K θ hq he u S hu
   have hz : Synthesis.Samples U Q S σ e (fun s=>here K (ρ s) (v s)) := fun i j hj=> (grace N M H U Q J K θ hq he v S hv i j hj).eases (by
      filter_upwards [D.cost,D.toSmall.positive] with s hs h; have hh:= h.trans_le hs; rw [abs_of_nonneg (by positivity : 0 ≤(ρ s)^j), abs_of_nonneg (by positivity : 0 ≤ (σ s)^j)]; gcongr)
   let X:=fun i=>(x i).ofLp; let Y:=fun i=>(y i).ofLp; let o':=fun i=>(o i).2
   have hh:=well_pitched D x y hx
   refine ⟨Office.phased D X Y o' M' δ hm hd hh U Q _ _ (fun i=>(o i).1) hl simple ht hz,?_⟩
   obtain ⟨C,hC,k,hk⟩:= Office.rated D X Y o' M' δ hm hd hh U Q _ _ (fun i=>(o i).1) hl simple 0 ht hz
   apply Paint.from_cost (C*3) (by positivity) k
   filter_upwards [D.toSmall.ran, D.toSmall.positive,D.cost,D.outer.bounded,hk] with i hi (hp:0<ρ i) hr (hq:σ i≤1) hk
   rw [mul_one]; apply hk.trans; have hx:=hp.trans_le hr; have ht : 0< OPE.Log.badge (D.r i):=zero_lt_one.trans_le hi;
   exact (mul_le_mul_of_nonneg_left (show |1+ Deck.radius D 0 i|≤ 3 from (by unfold Deck.radius; simp only [Nat.zero_add,pow_one]; rw [abs_of_nonneg (by positivity)]; linarith only [(div_le_one hx).mpr hr,hq])) (by positivity : 0≤ C*badge (D.r i)^k)).trans_eq (by ring)
-- transfer to through single-h horizon
omit hu hv in
lemma cost_lane (s:I→Tags G h (n+m)) (ha : ∀ i,Paint D.toSmall (fun _=>1) (fun l=>chair G h (s l i))):
    let Z i:= forest (x i) ((σ i / ρ i) • y i); let F i q := painted U K q (fun _:Fin (n+m)=>h) (ρ i) (Z i) (s i);
    Paint S σ (fun i=> F i (o i).1-F i none) ∧ Paint S (fun _=>1) (fun i=> F i (o i).1) := by
    intro z F; let X (i:I):Tags G h n:= s i ∘ Fin.castAdd m; let Y (i:I):Tags G h m:= s i ∘ Fin.natAdd n;
    obtain ⟨he',H'⟩:=balance N M H U Q J K θ hq he hl D X Y o hm hd x y hx (fun i=>ha (Fin.castAdd m i)) (fun i=>ha (Fin.natAdd n i))
    let L i o:= honest U K (ρ i) (σ i) o (x i) (y i) (X i) (Y i)
    have hf : ∀ᶠ i in D.p,∀ p:View U,L i p= F i p.1:= by
       filter_upwards [hx] with i hi p
       unfold F L; rw [show s i=Fin.append (X i) (Y i) from (by funext j; induction j using Fin.addCases with| left j=> rw [Fin.append_left]; rfl| right j=> rw [Fin.append_right]; rfl),show z i=forest _ _ from rfl,scale_story U K p.1 (D.r i) p.2 (x i) _ (X i) (Y i) (landed_slots _ _ hi hd), far_positions (ρ i) (σ i) _ _ hi.pos];rfl
    exact ⟨he'.assists (hf.mono fun i h=> congrArg₂ HSub.hSub (h (o i)) (h (none,(o i).2))), H'.assists (hf.mono fun i h=> h (o i))⟩
end
end
end YM.FVA2.GradedFar.Physical.Round
