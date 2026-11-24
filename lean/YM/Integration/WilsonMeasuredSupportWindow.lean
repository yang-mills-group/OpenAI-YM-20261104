import YM.Integration.WilsonMeasuredRetainedWing
import YM.LocalLTE.Quartz.Points
import YM.LocalLTE.Weft.Gem

/-! The complete connected physical low catalogue, its genuine retained Gaussian comparison and the requested localized quiet trace count. -/
set_option autoImplicit false

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredSupport
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))

structure Component (p : H.ThinP) (v : Finset (Veil c f)) (q : ℕ) : Prop where
  burns : Ac.Spark H.supportP p.val
  players : troupe T R Q.halo (radiusB t) p.val
  lift : p.val=Fan.arm v
  received : v.card≤q

structure Geometry (q : ℕ) : Prop where
  length : z.fst≤q
  each i : Component H (z.2 i) (East.docket H z i) q

structure Roster (q : ℕ) : Prop where
  can : Geometry H z q
  lives i : (D i).reach⊆(z.2 i).val

theorem of_candor (q n : ℕ) (r₀ : ℕ→ℕ) (A' : ι→Prop) (h : Candor M z D q n r₀ A') : Roster M H z D q :=
  ⟨⟨h.can.length,fun i=>⟨(h.can.each i).burns,(h.can.each i).players,(h.can.each i).lift,(h.can.each i).received⟩⟩,h.lives⟩

theorem original (q : ℕ) (hlow : ¬Height.tiredN H q z) (U : Config G c)
    (hU : Captain.wingTerm (χ:=χ) z M D U≠0) : Roster M H z D q := by
  have live (i : Option (Fin z.fst)) : Captain.waltz H χ M (z.2 i) (D i) U ≠ 0 := fun h=>hU (by
    unfold Captain.wingTerm; rw [Finset.prod_eq_zero (i:=i) (Finset.mem_univ i) h,mul_zero,zero_div])
  have terms i := Captain.silenced M (z.2 i) (D i) U (live i)
  have htrue i : Ac.Spark H.supportP (z.2 i).val ∧ troupe T R Q.halo (radiusB t) (z.2 i).val :=
    ⟨(terms i).1,(terms i).2.1⟩
  have cheap := Height.aged (H:=H) htrue hlow
  have labels := YM.Integration.WilsonLowMayerRoster.retained (H:=H) z hlow htrue
  refine ⟨⟨cheap.2.le,fun i=>?_⟩,fun i=>(terms i).2.2.1⟩
  have he (a : Veil c f) : a∈East.docket H z i ↔ Fan.elastic (S:=S) a∈(z.2 i).val :=
    Finset.mem_preimage (hf:=(Fan.runOut (S:=S)).injOn)
  have equal : (z.2 i).val = Fan.arm (East.docket H z i) := by
    ext a
    constructor
    · intro ha
      obtain ⟨r,rfl⟩:=labels i a ha
      exact Finset.mem_image.mpr ⟨r,(he r).2 ha,rfl⟩
    · intro ha
      obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp ha
      exact (he r).1 hr
  refine ⟨(htrue i).1,(htrue i).2,equal,?_⟩
  rw [←Finset.card_image_of_injective (East.docket H z i) (Fan.runOut (S:=S))]
  change (Fan.arm (East.docket H z i)).card≤q
  rw [←equal]
  exact (cheap.1 i).few

variable {α C B' v₁ d v₀ e A β κ :ℝ}(q k : ℕ) (hx : Roster M H z D q)
include hx
lemma weaving (p:Option (Fin z.fst)):
    let S:= z.2 p; let u:= D p; let V:=Captain.quietR M (z.2 p) u
    V⊆ East.docket H z p ∧ u.val.card ≤ q ∧ S.val \ u.reach= Fan.arm V:=by
     intro Y u v
     have hf (i:Veil c f): i∈v↔ elastic i∈Y.val\u.reach:= Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=S)|>.injOn)
     have h (i:Veil c f): i∈East.docket H z p↔ elastic i∈ Y.val:= Finset.mem_preimage (hf:=LocalLTE.Fan.runOut (S:=S)|>.injOn)
     have H' := hx.can.each p; have hK: Y.val = arm (East.docket H z p):= H'.lift
     refine ⟨fun i hi=>(h i).2 (Finset.mem_sdiff.mp ((hf _).1 hi)).1, ?_,?_⟩
     · have he: u.reach.card=u.val.card:= card_image_of_injOn u.property -- edit
       have hh: u.reach ⊆ Y.val:= hx.lives p
       rw [← he]; refine le_trans (card_le_card hh) ?_; rw [hK,arm, card_image_of_injective _ LocalLTE.Fan.runOut]; exact H'.received
     ext i; constructor
     · intro hi; have ht:i∈ Y.val:=(Finset.mem_sdiff.mp hi).1; rw [hK] at ht; obtain ⟨j,hh,rfl⟩:=mem_image.mp ht; exact mem_image_of_mem _ ((hf _).2 hi)
     intro hi; obtain ⟨j,h,rfl⟩:=mem_image.mp hi; exact (hf _).1 h
lemma ilk (p:Option (Fin z.fst)) (r:Greenbelt.Reserve S)(q':S.Choices)(y:Disk G c)(U:Config G c)(ha:U=increment (1:Config G c) y.2): let i:=z.2 p; let A:=((Greenbelt.prism T t χ o.K U (Greenbelt.allot r)))
      let K':=(Matter.preps A (roster i.val)).taggedL q'; K'=timeΛ ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL q') y:=by
    intro i A K'; have hR:roster i.val= (⟨∅,∅,∅⟩:Stores S):= by rw [show i.val=_ from (hx.can.each p|>.lift), Field.rosterD] -- orientation eq
    unfold K' A; rw [hR,ha]; rfl
local notation "TZ"=> Disk G c
variable (C₁: Captain H j C d v₀ e B' v₁ y B η k χ)
    (hK: Daisy.HostQ H C₁.conduit B' B k)
include C₁
lemma shutter (p:Option (Fin z.fst))(x:Disk G c)(U:Config G c)(he:U=increment (1:Config G c) x.2)(hF: flags (Pressure.temp t) U=∅):
    let i:= z.2 p; let d:= D p
    waltz H χ M i d U=likely fun r:Greenbelt.Reserve S=> likely fun k': S.Choices=>
       (team M d).qlocal4a_cinema (timeΛ ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL k') x) i.val W o.a Q.table Q.halo (Fan.fibers H i):=by
   intro i d; apply congr_arg likely; funext r
   let X := Greenbelt.prism T t χ o.K U (Greenbelt.allot r)
   let f:=team M d; have hz : Healthy (Pressure.temp t) (H.smallAt i) X.V:=by change Disjoint _ (flags _ U); rw [hF];simp
   have hΨ:= Team.qlocal4a_arc f X i.val H C₁.oboe rfl rfl rfl i.2.2 hz (y:=(0:ℝ)) (show Mode (fun _:ℝ=> X.V) _ j v₀ from ⟨C₁.position.le, fun i=> a_oneB G _ C₁.position.le⟩) rfl
   change f.qlocal4a_picture X i.val W o.a Q.table Q.halo=_; rw [show f.qlocal4a_picture X i.val W o.a Q.table Q.halo=_ from hΨ.self_of_nhds]; unfold Team.qlocal4a_grove
   rw [if_pos ⟨hx.can.each p|>.burns,hx.can.each p|>.players⟩]; refine congr_arg likely (funext fun k'=> ?_)
   exact congr_arg (fun K=> f.qlocal4a_cinema K i.val W o.a Q.table Q.halo (Fan.fibers H i)) (ilk M H χ z D q hx p r k' x U he)
end YM.LocalLTE.Fan.MeasuredSupport

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredOpenWing
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q k : ℕ) (r₀ : ℕ→ℕ) (hx : MeasuredSupport.Roster M H z D q)


variable (C₁: Captain H j C d v₀ e B' v₁ y B η k χ)
    (hK: Daisy.HostQ H C₁.conduit B' B k)
local notation "ℙ"=> (fun i=> (Merge.Palette.team M (D i)).weight)
variable (reserve : ℝ) (fee : Veil c f → ℝ)
local notation "Bv" => reserve
local notation "Z" => fee
local notation "mΦ" => (fun i => (M i).ingredient)
variable (hC : ∀ i : Option (Fin z.fst), ∀ v∈Captain.quietR M (z.2 i) (D i), 0 ≤ fee v ∧ fee v ≤ 1)
include hx hC C₁
local notation "TZ" => Disk G c
local notation "Ξ" => (2+Real.exp 1)
theorem averaged (Q':ℝ) (hp0:0 ≤ Q') (u:Directions G c) (hV: flags (Pressure.temp t) (increment (1:Config G c) u)=∅)(hT:Stamp T)(m:ℕ)(hB:1≤reserve)
    (hp:let x: Disk G c:=(gStep R.beta,u); ∀ (i:Option (Fin z.fst))(F:Forest S.ratio)(X:Coat T F),X.x=t→X.width=o.K→X.χ=χ→(timeΛ X x).manifest→ (Fan.pool (Fan.fibers H (z.2 i)) X x).real (cabinet (Fan.fibers H (z.2 i)) (postponement L t o))ᶜ ≤ Q' ∧ ∀ j∈Captain.quietR M (z.2 i) (D i),∀ b:Air f G, |vows X R Q o.a x b j| ≤ fee j*reserve^(levy r₀ j)):
    let x:TZ:=(gStep R.beta,u);
    |wingTerm (χ:=χ) z M D (increment 1 u)- Field.speedΛ H z.2 * mica M mΦ H χ z D m x| ≤ |Field.speedΛ H z.2| * canvasX M H z D Z * budgetAt q z.1 m Bv Q':=by
    intro x
    let Y:= increment (1:Config G c) u; let V i:= z.2 i; let Z' (i):=quietR M (V i) (D i); let ℓ:=Field.speedΛ H z.2; let g i:= waltz H χ M (z.2 i) (D i) Y; let f' i:= Fan.pinV M mΦ H χ (V i) (D i) m x -- infer order
    have hc(i) :=MeasuredSupport.shutter M H χ z D q k hx C₁ i x Y rfl hV
    have hS(i):=MeasuredSupport.weaving M H z D q hx i
    let E':=Veil c f; let ξ: E'→ℝ:= Z; let K:=Bv; let θ:ℝ:= (Ξ)^q; let U(i):ℝ:=ℙ i*∏ j∈ Z' i,ξ j; let η:=Q'+q*(K^Pastel.mini)^m
    have hU(i):0 ≤ U i:=mul_nonneg (team M (D i)|>.profit) (prod_nonneg (fun j hj=> (hC _ _ hj).1)); have hθ:(0:ℝ) ≤ θ:=by unfold θ; positivity
    have hη:0 ≤ η:=by unfold η; positivity
    letI : Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
    have h(i): |f' i| ≤ U i*θ ∧ |g i-f' i| ≤ U i*θ*η:=by
       let X'(r:Reserve S)(z:S.Choices):= (prism T t χ o.K (1:Config G c) (allot r)).taggedL z
       let Y'(r:Reserve S)(u:S.Choices):= Fan.wishes (L:=L) (o:=o) M mΦ Q (D i) (X' r u) (Z' i) (fibers H (V i)) t m x
       let Q₁(r:Reserve S)(u:S.Choices):= (team M (D i)).qlocal4a_cinema (timeΛ (X' r u) x) (V i).val W o.a Q.table Q.halo (Fan.fibers H (V i))
       let b:= (Z' i).card; have hb:b≤ q:= (card_le_card (hS i|>.1)).trans (hx.can.each i|>.received)
       have ht : ℙ i*((Ξ)^b*(∏ j∈Z' i,ξ j)) ≤ U i*θ:= by rw [mul_left_comm,← show U i=_ from rfl,mul_comm];apply mul_le_mul_of_nonneg_left _ (hU i); exact pow_le_pow_right₀ (by linarith [Real.exp_pos 1]) hb
       have h'(r:Reserve S)(u':S.Choices): ‖Y' r u'‖ ≤ U i*θ∧ |Q₁ r u'-Y' r u'| ≤ U i*θ*η:=by
          let P:=X' r u'; have hg:= hp i _ P rfl rfl rfl (show (timeΛ P x).manifest from hV.symm)
          obtain ⟨h1,h2⟩:= MeasuredCinema.component M Q (D i) H P x (Z' i) (V i).val (hx.lives i) (hS i|>.2.2) (Fan.fibers H (V i)) rfl rfl (show (timeΛ P x).manifest from hV.symm) hB r₀ ξ (fun j hj=> ⟨(hC _ _ hj|>.1),(hC _ _ hj|>.2),fun b=> (hg.2 _ hj b)⟩) hT u rfl m Q' hg.1 -- order
          refine ⟨h1.trans ht,h2.trans (mul_le_mul ht (show Q'+b*(K^mini)^m ≤ η from ?_) (by positivity) (mul_nonneg (hU _) hθ))⟩
          unfold η; gcongr
       have hp:f' i=likely (fun r:Reserve S=> likely (Y' r)):=rfl
       rw [hp,show g i=likely (fun r:Reserve S=> likely (Q₁ r)) from hc i]
       refine ⟨Field.avgBound _ (fun i=>Field.avgBound _ (fun j=> (h' i j).1)),Field.difference _ _ (fun i=> Field.difference _ _ (fun j=> (h' i j).2))⟩ -- order
    let p i:=U i*(θ*(1+η))
    have he i:0≤p i:=mul_nonneg (hU i) (mul_nonneg hθ (add_nonneg zero_le_one hη))
    have hf₀ : (∏ i,p i)= canvasX M H z D ξ*(θ*(1+η))^(z.fst+1):= by unfold p; rw [prod_mul_distrib,prod_const]; simp_rw [card_univ,Fintype.card_option,Fintype.card_fin]; rfl
    have he0 i: U i*θ ≤ p i:= by unfold p; rw [←mul_assoc]; exact le_mul_of_one_le_right (mul_nonneg (hU i) hθ) (le_add_of_nonneg_right hη)
    rw [show wingTerm (χ:=χ) z M D (increment 1 u)= ℓ*(∏ i,g i) from (by unfold g ℓ Captain.wingTerm Field.speedΛ;dsimp only; ring)];change |ℓ*(∏ i,g i)-ℓ*(∏ i,f' i)|≤ _; rw [← mul_sub,abs_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg ℓ)
    refine le_trans (Bakers.price hη Finset.univ g f' p (fun i _=> he i) (fun i _=> ?_) (fun i _=>(h i).1.trans (he0 i)) (fun i _=>?_)) (?_)
    · have hΓ:=(abs_add_le (g i-f' i) (f' i)); rw [sub_add_cancel] at hΓ; refine hΓ.trans ((add_le_add (h i).2 (h i).1).trans_eq ?_); unfold p; ring
    · have ht':=(h i).2; rw [mul_comm η]; exact ht'.trans (mul_le_mul_of_nonneg_right (he0 i) hη)
    rw [hf₀,card_univ,Fintype.card_option,Fintype.card_fin]; change _≤ canvasX M H z D ξ*((↑(z.fst+1):ℝ)*η*(θ*(1+η))^(z.fst+1)); exact le_of_eq (by ring)

end YM.LocalLTE.Fan.MeasuredOpenWing

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredWingAmount
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (H:Cash W t μ L Q o a T R)(χ:Chi)
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q k : ℕ) (hx : MeasuredSupport.Roster M H z D q)


variable (C₁: Captain H j C d v₀ e B' v₁ y B η k χ)
    (hK: Daisy.HostQ H C₁.conduit B' B k)

local notation "V"=> (fun i=> (z.2 i).val)
local notation "T₀"=> (fun i=> Captain.quietR M (z.2 i) (D i))
local notation "P"=> (fun i=> (Merge.Palette.team M (D i)).weight)

/-- All physical roots retain their one independently priced geometric shape. -/
def protection (l : ℕ) := ∏i : Option (Fin z.fst), (1+H.shapeW (z.2 i).val)^l

theorem protect (l : ℕ) (hl : 1≤l) (i : Option (Fin z.fst)) :
    1≤protection H z l ∧ H.shapeW (z.2 i).val≤protection H z l := by
  let f (j : Option (Fin z.fst)) := (1+H.shapeW (z.2 j).val)^l
  have hf j : 1≤f j := one_le_pow₀ (by linarith [H.positive_volume (z.2 j).val])
  refine ⟨Finset.one_le_prod (fun j _=>hf j),?_⟩
  have hi : f i≤protection H z l := by
    change f i≤∏j,f j
    rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact le_mul_of_one_le_right (zero_le_one.trans (hf i)) (Finset.one_le_prod (fun j _=>hf j))
  apply le_trans _ hi
  calc _ ≤ (1+H.shapeW (z.2 i).val)^1 := by simp
       _ ≤ _ := pow_le_pow_right₀ (by linarith [H.positive_volume (z.2 i).val]) hl

include hx in
theorem quiet_count (h : ¬Height.tiredN H q z) : ∑ i, (T₀ i).card ≤ q := by
  have he i := (MeasuredSupport.weaving M H z D q hx i).2.2
  have per i : (T₀ i).card ≤ (V i).card := by
    calc _ = (Fan.arm (S:=S) (T₀ i)).card := (Finset.card_image_of_injective _ (Fan.runOut (S:=S))).symm
         _ = ((V i) \ (D i).reach).card := congrArg Finset.card (he i).symm
         _ ≤ _ := Finset.card_le_card Finset.sdiff_subset
  have total : ∑i,(T₀ i).card ≤ Height.breadth H z := Finset.sum_le_sum fun i _=>per i
  have ht := lt_of_not_ge (not_or.mp h).1
  unfold Height.degreeN at ht
  omega

include hx C₁ in
theorem funded (h : ¬Height.tiredN H q z) (hB : 1≤B) (w : Veil c f → ℝ) (A₀ : ℝ) (hA : 1≤ A₀)
    (hw : ∀i, ∀v∈T₀ i, 0≤w v ∧ w v≤ A₀*C₁.conduit.fare (Fan.elastic (S:=S) v)) :
    |Field.speedΛ H z.2| * (Fan.canvasX M H z D w * protection H z k) ≤ A₀^q * Captain.wingBill C₁ z M D := by
  let γ i := ∏v∈T₀ i,C₁.conduit.fare (Fan.elastic (S:=S) v)
  let c i := P i * γ i
  let f i := (1+H.shapeW (V i))^k
  have hp i : 0≤P i := (Merge.Palette.team M (D i)).profit
  have hc i : 0≤c i := mul_nonneg (hp i) (Finset.prod_nonneg fun _ _=> C₁.conduit.fares _)
  have hfs i : 0≤f i := pow_nonneg (by linarith [H.positive_volume (V i)]) _
  have hbills (i : Option (Fin z.fst)) : c i * f i ≤ Captain.winhit C₁ M (z.2 i) (D i) := by
    have he := (MeasuredSupport.weaving M H z D q hx i).2.2
    have occ : H.ticketsP 0 0 0 (V i) := ⟨(hx.can.each i).burns,Nat.zero_le _,Nat.zero_le _,H.positive_volume _⟩
    have bids : ∏ t∈(V i)\(D i).reach,C₁.conduit.fare t = γ i := by
      rw [he]; unfold Fan.arm γ; exact Finset.prod_image (Fan.runOut (S:=S)).injOn
    unfold Captain.winhit Captain.inlet
    rw [if_pos ⟨occ,hx.lives i⟩,bids]
    change c i*f i ≤ (2:ℝ)^j*(B*(c i*f i))
    exact (le_mul_of_one_le_left (mul_nonneg (hc i) (hfs i)) hB).trans
      (le_mul_of_one_le_left (mul_nonneg C₁.balance (mul_nonneg (hc i) (hfs i))) (one_le_pow₀ (by norm_num)))
  have component (i : Option (Fin z.fst)) : P i * (∏v∈T₀ i,w v) ≤ A₀^(T₀ i).card * c i := by
    have he : ∏v∈T₀ i,w v ≤ ∏v∈T₀ i,A₀*C₁.conduit.fare (Fan.elastic (S:=S) v) :=
      Finset.prod_le_prod (fun v hv=>(hw i v hv).1) fun v hv=>(hw i v hv).2
    have h' := mul_le_mul_of_nonneg_left he (hp i)
    rw [Finset.prod_mul_distrib,Finset.prod_const] at h'
    exact h'.trans_eq (by unfold c γ; ring)
  have hhome : ∏i,c i*f i ≤ ∏i,Captain.winhit C₁ M (z.2 i) (D i) := Finset.prod_le_prod
    (fun i _=>mul_nonneg (hc i) (hfs i)) (fun i _=>hbills i)
  have hrows := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>mul_nonneg (hp i) (Finset.prod_nonneg fun v hv=>(hw i v hv).1))
    (fun i _=>component i)
  have hpow : (∏i,A₀^(T₀ i).card*c i)=A₀^(∑i,(T₀ i).card)*∏i,c i := by
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [hpow] at hrows
  have he : Fan.canvasX M H z D w ≤ A₀^q * ∏i,c i := hrows.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hA (quiet_count M H z D q hx h)) (Finset.prod_nonneg fun i _=>hc i))
  have ff : (∏i,f i)=protection H z k := rfl
  have hfprod : 0≤∏i:Option (Fin z.1),f i:=Finset.prod_nonneg fun i _=>hfs i
  have eqf : (∏i,c i)*(∏i,f i)=∏i,c i*f i:=Finset.prod_mul_distrib.symm
  have ht : canvasX M H z D w*(∏i,f i) ≤ A₀^q*∏i,c i*f i:=by
    calc _ ≤ (A₀^q*∏i,c i)*(∏i,f i):=mul_le_mul_of_nonneg_right he hfprod
         _ = _:=by rw [mul_assoc,eqf]
  have htar := ht.trans (mul_le_mul_of_nonneg_left hhome (pow_nonneg (zero_le_one.trans hA) _))
  calc _ ≤ |Field.speedΛ H z.2| * (A₀^q* ∏i,Captain.winhit C₁ M (z.2 i) (D i)) :=
         mul_le_mul_of_nonneg_left htar (abs_nonneg _)
       _ = _ := by unfold Field.speedΛ Captain.wingBill; rw [abs_div,abs_of_nonneg (by positivity : 0≤((z.fst+1).factorial:ℝ))]; ring

end YM.LocalLTE.Fan.MeasuredWingAmount

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredWishPortfolio
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner

variable {ι : Type} [Fintype ι] (M : ι → Lotus.Leaf R) (H : Cash W t μ L Q o a T R)

/-- The true finite two-portfolio count at an occupied coarse site. -/
def amount (L : Side) (q halo : ℕ) (t : ℝ) : ℝ :=
  Fan.stageQ ((Animals.ballCost (East.stagnate q halo*radiusB t):ℝ)*(East.grand L:ℝ)) 1 q

theorem rate (q halo : ℕ) : Rate G L 0 (amount L q halo) := by
  have h : Rate G L 0 (fun t=>(Animals.ballCost (East.stagnate q halo*radiusB t):ℝ)) := by
    simpa using Census.width_rate G L (East.stagnate q halo) 0
  exact Fan.springsQ q _ (h.mul_right (East.grand L:ℝ)) 1

omit [Fintype ι] in
theorem site (q n : ℕ) (r₀ : ℕ→ℕ) (eligible : ι→Prop) (φ : ℕ→ℝ)
    (hφ : ∀ a,SumBudget (fun i=>if (R.activities.reg i).site=a then φ i else 0) 1)
    (w : ι→ℝ) (hw : ∀ i,0≤w i) (cost : SumBudget (Merge.Palette.wages M w) 1)
    (u : Site c) :
    SumBudget (fun z : Fan.Stars H M=>if u∈Captain.reachability z.1 ∧
      Candor M z.1 z.2 q n r₀ eligible then
      Fan.beryl M H (Fan.ratioCash R (East.jewel P L t) φ) w z else 0)
      (amount L q Q.halo t) := by
  have rows := East.highwayQ H φ hφ
  apply Fan.tiers M H q n r₀ eligible _ _ w hw u _ cost
  · exact fun i=>(rows.1 i).1
  · exact budget_loosen (rows.2 _) (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Animals.neighbors_card ..)) (Nat.cast_nonneg (East.grand L)))

omit [Fintype ι] in
/-- This permits all original physical tests, any further true cutoff, and any signed subseries. -/
theorem portfolio (q n : ℕ) (r₀ : ℕ→ℕ) (eligible : ι→Prop) (φ : ℕ→ℝ)
    (hφ : ∀ a,SumBudget (fun i=>if (R.activities.reg i).site=a then φ i else 0) 1)
    (w : ι→ℝ) (hw : ∀ i,0≤w i) (cost : SumBudget (Merge.Palette.wages M w) 1)
    (u : Site c) (a : Fan.Stars H M→ℝ) (ha : ∀ z,0≤a z)
    (head : ∀ z,a z≠0→u∈Captain.reachability z.1 ∧ Candor M z.1 z.2 q n r₀ eligible)
    (bound : ∀ z,a z≤Fan.beryl M H (Fan.ratioCash R (East.jewel P L t) φ) w z) :
    SumBudget a (amount L q Q.halo t) := by
  refine budget_mono (site M H q n r₀ eligible φ hφ w hw cost u) ha (fun z=>?_)
  split
  · exact bound z
  · next hn => exact (not_ne_iff.mp (fun h=>hn (head z h))).le

end YM.LocalLTE.Fan.MeasuredWishPortfolio

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredTrace
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι':ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable (q : ℕ)



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.
variable (φ':Veil c f→ℝ) (h':∀ i,0≤φ' i) (rA:ι→ℝ) (hr:∀ i,0≤rA i)
local notation "Y'"=> betaF G t L
local notation "Ω"=> Merge.Tickets (Merge.Palette.sign M S)


/-- All quiet retained original labels on one authentic signed cluster lie in its common physical register. -/
def seen (J : Finset (Site c)) : Prop := ∀ i j, j∈Captain.quietR M (z.2 i) (D i) → East.traceO S R j∈J

variable {W' V : ℝ} (J : Finset (Site c))
  (ht : SumBudget (fun i=>if East.traceO S R i∈J then φ' i else 0) V)
  (hp : SumBudget (Merge.Palette.wages M rA) W')
include ht hp h' hr
set_option maxHeartbeats 200000 in
lemma visits (p:ℕ) :
    SumBudget (fun z:Steps H M p=> if seen M H ⟨p,z.1⟩ z.2 J ∧ MeasuredSupport.Roster M H ⟨p,z.1⟩ z.2 q then Fan.beryl M H φ' rA (Fan.sift M H p z) else 0) (East.tonic p *((rack V q*rack W' q)^(p+1))):=by
   let P:= Steps H M p; let R'α:=Option (Fin p)
   let a' (i:P):= i.1; let b' (i:P):=i.2; let Q' (i:P):Prop:=seen M H ⟨p,i.1⟩ i.2 J ∧ MeasuredSupport.Roster M H ⟨p,i.1⟩ i.2 q
   let K(i:P): R'α → Finset (Veil c f) × Ω:= fun j=> (quietR M (a' i j) (b' i j), b' i j)
   have hs(i:P)(he:Q' i)(j:R'α):= MeasuredSupport.weaving M H ⟨p,a' i⟩ (b' i) q he.2 j
   have hk: Set.InjOn K {i|Q' i}:=by
       intro i hi j hj h; change Q' i at hi; change Q' j at hj
       have hx u: (K i u).2=(K j u).2:= congr_arg Prod.snd (congr_fun h u)
       apply Prod.ext; swap; · exact funext hx
       funext v; apply Subtype.ext
       let A (i:P):= (K i v).2.reach; have he (i:P) (h:Q' i): (i.1 v).val= Fan.arm (K i v).1 ∪ (A i):=by
          rw [← show (i.1 v).val \ A i= Fan.arm (K i v).1 from hs i h v|>.2.2]
          exact Eq.symm (sdiff_union_of_subset (h.2.lives _))
       rw [he i hi,he j hj]; unfold A; rw [h]
   let f₀ i:= if East.traceO S R i∈J then φ' i else 0
   let V'(P:Ω):ℝ:= if P.val.card ≤ q then ∏ j∈ P.val,wages M rA j else 0
   let L'(D:Finset (Veil c f)):= if D.card ≤ q then ∏ i∈D,f₀ i else 0
   have he:SumBudget V' (rack W' q):=budget_pull (Subtype.val (p:= Draft (Merge.Palette.sign M S))) Subtype.val_injective (budget_grace q hp) -- edit
   have hy:SumBudget L' (rack V q):= budget_grace q ht
   let z' (i: R'α → Finset (Veil c f) × Ω):= ∏ j,L' (i j).1 * V' (i j).2
   have hB:= budget_seat (budget_prod hy he) (Option (Fin p)); rw [Fintype.card_option,Fintype.card_fin] at hB
   have hg:= budget_scale (endowed p) (East.indicatorPull K hk z' hB)
   refine budget_mono hg (fun i=> ?_) (fun i=> ?_)
   · split; exact Fan.charmNN M H φ' h' rA hr _; rfl
   change (if Q' i then beryl M H φ' rA (Fan.sift M H p i) else 0) ≤(East.tonic p:ℝ)*(@ite ℝ (Q' i) (Classical.propDecidable (Q' i)) (z' (K i)) 0); by_cases H': Q' i
   swap; · simp_rw [if_neg H',mul_zero]; exact le_rfl
   rw [if_pos H', if_pos H']
   let T (j):=K i j; let u' : H.fragrances:= ⟨p,i.1⟩; let Qd:= East.docket H ⟨p,a' i⟩; let Y:= b' i
   have he'(j:R'α)(p:Veil c f) (h:p∈(T j).1): f₀ p=φ' p:= if_pos (H'.1 j p h)
   have hW (j:R'α): L' (T j).1=∏ i∈ (T j).1,φ' i:=by unfold L'; rw [if_pos ((card_le_card (hs i H' j|>.1)).trans (H'.2.can.each j|>.received))]; exact prod_congr rfl (he' j)
   have hc(j:R'α): V' (T j).2=(Palette.team M (Y j)).weight*∏ k∈(Y j).val,rA k:=by unfold V'; rw [if_pos (hs i H' j|>.2.1),Palette.worth]; unfold Palette.wages; rw [prod_mul_distrib,mul_comm]; -- edit rfl
   have ht : z' (K i)= (canvasX M H u' (i.2) φ')* pearl u' M rA i.2:= by
      unfold canvasX pearl; rw [← prod_mul_distrib]; refine Finset.prod_congr rfl fun v _=>?_ ; change L' (T v).1* V' (T v).2=_; rw [hW,hc]; unfold T K Y b' a' u'; dsimp; ring_nf
   let P':= pearl u' M rA i.2; have hh:0 ≤ P':=prod_nonneg fun j _=> prod_nonneg fun i _=> hr i
   unfold beryl; rw [mul_assoc]; apply le_trans (mul_le_mul_of_nonneg_right (East.ballads ..) (mul_nonneg (prod_nonneg fun i _=>mul_nonneg (Team.profit _) (prod_nonneg fun i _=> h' i)) hh)); exact le_of_eq (congr_arg (_* ·) ht.symm)
private noncomputable def walksQ : Stars H M ≃ Σ n:ℕ,Steps H M n where
    toFun z:=⟨z.1.fst,z.1.2,z.2⟩
    invFun k:= sift M H k.1 k.2
    left_inv _:=rfl
    right_inv _:=rfl

include ht hp h' hr
lemma tiers : SumBudget (fun z:Stars H M=> if seen M H z.1 z.2 J ∧ MeasuredSupport.Roster M H z.1 z.2 q then Fan.beryl M H φ' rA z else 0) (stageQ V W' q):=by
   let X(i:ℕ):= tonic i*(rack V q*rack W' q)^(i+1); let D:=Finset.range (q+1); let f i:= if i∈D then X i else 0
   have he(i):0 ≤ X i:= mul_nonneg (East.endowed _) (pow_nonneg (mul_nonneg (East.treasury _ (budget_nonneg ht) _) (East.treasury _ (budget_nonneg hp) _)) _)
   have h : SumBudget f (stageQ V W' q) := by
       refine budget_of_sum (fun i=> ?_) fun i=> ?_
       · unfold f; split; exact he i; rfl
       unfold f; rw [← sum_filter]; exact sum_le_sum_of_subset_of_nonneg (fun a ha=> (mem_filter.mp ha).2) (fun i _ _=> he i)
   let g (z:Stars H M):= if seen M H z.1 z.2 J ∧ MeasuredSupport.Roster M H z.1 z.2 q then Fan.beryl M H φ' rA z else 0
   let e:=walksQ M H; refine budget_pull e e.injective (show SumBudget (fun i=>g (e.symm i)) _ from sigma_total _ f ?_ h) -- budget implicit at f ◦ .s refine
   intro i; unfold f; split
   next h => exact visits M H q φ' h' rA hr J ht hp _ -- ites
   next h =>
     convert (show SumBudget (fun _ : Steps H M i=> (0:ℝ)) 0 from by simp [SumBudget]) using 1; funext j
     apply if_neg; intro hj
     exact h (Finset.mem_range.mpr (show i<q+1 from Nat.lt_add_one_of_le hj.2.can.length))

omit ht hp h' in
/-- Every retained physical gate inside any finite measured register has period-free submitted cost. -/
theorem native (J : Finset (Site c)) (φ₀ : ℕ→ℝ)
    (hφ : ∀a,SumBudget (fun i=>if (R.activities.reg i).site=a then φ₀ i else 0) 1)
    (hp₀ : SumBudget (Merge.Palette.wages M rA) 1) :
    SumBudget (fun z : Fan.Stars H M=>if seen M H z.1 z.2 J ∧ MeasuredSupport.Roster M H z.1 z.2 q then
      Fan.beryl M H (Fan.ratioCash R (East.jewel P L t) φ₀) rA z else 0)
      (Fan.stageQ ((J.card:ℝ)*(East.grand L:ℝ)) 1 q) := by
  have rows := East.highwayQ H φ₀ hφ
  exact tiers M H q _ (fun i=>(rows.1 i).1) rA hr J (rows.2 J) hp₀

end YM.LocalLTE.Fan.MeasuredTrace

noncomputable section
namespace YM.LocalLTE.Fan.MeasuredTraceAperture
open YM.PhysicalNext.Repeat.Deck
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
section meter
variable (n) (i:H.ThinP) (u:Merge.Tickets (Merge.Palette.sign M S))
def fibers :=podium S G (H.unionP i.val) (radiusB t) -- `H` pr
local notation "S'"=> Fan.fibers H i
def pinV (m:ℕ) (p:Disk G c):= likely fun r:Greenbelt.Reserve S=> likely fun q:S.Choices=>
    Fan.wishes (o:=o) (L:=L) M φ Q u ((Greenbelt.prism T t χ o.K (1:Config G c) (Greenbelt.allot r)).taggedL q) (Captain.quietR M i u) S' t m p
end meter
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))



/-- The center belongs to the original physical support even for an arbitrarily long old row or path. -/
theorem anchor (v : Veil c f) : East.traceO S R v∈H.supportP (Fan.elastic v) := by
  rcases v with i|i
  · exact (Brim.plate H i).anchor
  · have h := PhysicalNext.Repeat.Deck.Mint.centered Q.halo (radiusB t) (Mint.verse R.path i) (Brim.paidB H) i S T R le_rfl
    change Mint.pace S i∈H.supportP (Fan.elastic (Sum.inr i))
    rw [show Fan.elastic (S:=S) (Sum.inr i)=Mint.disc S i from by rcases i with i|i|i|i <;>rfl]
    exact h.1

theorem union (q : ℕ) (h : MeasuredSupport.Roster M H z D q)
    (i : Option (Fin z.fst)) (v : Veil c f) (hv : v∈Captain.quietR M (z.2 i) (D i)) :
    East.traceO S R v∈Captain.reachability z := by
  have hh := (MeasuredSupport.weaving M H z D q h i).1 hv
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,show East.traceO S R v∈H.unionP (z.2 i).val from
    Finset.mem_biUnion.mpr ⟨Fan.elastic v,(h.can.each i).lift.symm ▸ Finset.mem_image_of_mem _ hh,anchor H v⟩⟩

def radius (b k : ℕ) := k*(4*b+2)+2*b

theorem registered (q : ℕ) (h : MeasuredSupport.Roster M H z D q) (k : ℕ) (x : Site c)
    (hx : x∈Captain.reachability z) (hk : coverNumber (radiusB t) (Captain.reachability z)≤k) :
    MeasuredTrace.seen M H z D (Animals.neighbors (radius (radiusB t) k) x) := by
  intro i v hv
  apply (Animals.neighbors_mem ..).2
  exact (Corona.extent _ (radiusB t) hx (union M H z D q h i v hv)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) _)

def bill (L : Side) (b k q : ℕ) := Fan.stageQ ((Animals.ballCost (radius b k):ℝ)*(East.grand L:ℝ)) 1 q

theorem whole (q k : ℕ) (x : Site c) (φ : ℕ→ℝ)
    (hφ : ∀a,SumBudget (fun i=>if (R.activities.reg i).site=a then φ i else 0) 1)
    (w : ι→ℝ) (hw : ∀i,0≤w i) (paid : SumBudget (Merge.Palette.wages M w) 1) :
    let r:=Fan.ratioCash (c:=c) R (East.jewel P L t) φ
    SumBudget (fun a : Fan.Stars H M=>if x∈Captain.reachability a.1 ∧ coverNumber (radiusB t) (Captain.reachability a.1)≤k ∧
      MeasuredSupport.Roster M H a.1 a.2 q then Fan.beryl M H r w a else 0) (bill L (radiusB t) k q) := by
  intro r
  let J:=Animals.neighbors (radius (radiusB t) k) x
  have rows := East.highwayQ H φ hφ
  have he := budget_loosen (rows.2 J) (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Animals.neighbors_card (radius (radiusB t) k) x)) (Nat.cast_nonneg (East.grand L)))
  have hcount := MeasuredTrace.tiers M H q r (fun i=>(rows.1 i).1) w hw J he paid
  refine budget_mono hcount (fun v=>?_) (fun v=>?_)
  · split; exact Fan.charmNN M H r (fun i=>(rows.1 i).1) w hw _; rfl
  · split
    · next hz => exact le_of_eq (if_pos ⟨registered M H v.1 v.2 q hz.2.2 k x hz.1 hz.2.1,hz.2.2⟩).symm
    · exact hcount.1 _

end YM.LocalLTE.Fan.MeasuredTraceAperture
