import YM.MSbar.Jade.Pearl
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Jade
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P0"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
local notation "H"=>mold R F v
variable (X Y:Support f)(U':Config G f) (t:ℝ)(Z:Positions (Primary c G))
local notation "Λ"=> includeX (G:=G) F X
local notation "X₀"=>SpaceP F X G
local notation "χ!"=>(pinch (includeX (G:=G) F X) H)⁻¹
variable (e:PathData G)(l:Clip)(ρ:fieldDir G c 1→ AxisChart G F)
local notation "ν"=>vest (priced F v R.clip R.path) (t • Z)
local notation "f1"=>linCash F (t • Z)
open Next.SectorChange
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "r₀"=>rental F J R Y v (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "µ"=> c! ∘ includeX (G:=G) F X
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
local notation "S!"=> clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U'
local notation "D!"=> Bakery.Film.draw F X U' (c! ∘ includeX F X) t
local notation "F!"=> fun z:SpaceP F X G=> fLog F X χ t z (c!∘ includeX F X) U' r₀ (show Matrix (Lake F X G) (Lake F X G) ℝ from (pinch (includeX F X) H)⁻¹)
variable (ht:0<t)(u x:SpaceP F X G)
include ht
local notation "Q₀"=> chambers F Y J (postcard G c t Z) ν
local notation "W"=> postcard G c t Z
lemma tries : t • berth F R v J X Y U' Z t x= sampleY F R v J X Y U' (t • Z)+ imbed Λ*ᵥ (t •x):=by unfold berth; rw [smul_add, smul_inv_smul₀ ht.ne', Matrix.mulVec_smul] -- notation precedence
variable (hU:U'∈ hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B)
include h hU
lemma sweet (hx:x∈ clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U') : (imageNear J F) (chambers F Y J (postcard G c t Z) ν (D! x))= t • A! x ∧
          Q₀ (D! x)= Bakery.Film.stretch F (t • A! x):=by
    obtain ⟨-,-,hx',-⟩:= h.exports U' hU t ht; obtain ⟨h',he⟩:=hx' x hx; rw [show t • A! x=_ from tries F R v J X Y U' t Z ht x]; exact ⟨h',he⟩ -- args order
lemma applies (hx:x∈ clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U') : Q₀ (D! x)= postcard G f t (stamp F G (A! x)):=by
     rw [(sweet F R v J χ X Y U' t Z h ht x hU hx).2, postcard,← map_smul (stamp ..), tango]; rfl -- input order χ
variable (hp :X ⊆Y)(ha:LocalRatio χ)(hv:Clear G J)
include hp ha hv
lemma ballot (hx:x∈clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U') : ∀ i:F.Free, cord F i G (t • meetVar Z (berth F R v J X Y U' Z t x))∈Metric.ball 0 χ.radius:=by
   intro i; have he: cord F i G (t • meetVar Z (A! x))= tint G _ (imageNear J F (Q₀ (D! x))) i:=by rw [(sweet F R v J χ X Y U' t Z h ht x hU hx).1,_root_.map_smul,_root_.map_smul]; rfl
   rw [he]; exact anchors J F X Y _ _ χ hv _ h.seat hp (D! x) (show D! x∈ I! A B from hx.1)|>.2 i|>.1
-- relate partial Jacobian ∆ to full.
lemma arcSign (hx:x∈clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U'): Real.log (pay χ (tape ((c!∘ includeX F X)+t•x:X₀)))= ∑ i: F.Free, if hi:i∈ board F X then Real.log (χ.scale*χ.J ((cord F i G) (t • meetVar Z (berth F R v J X Y U' Z t x)))) else 0:=by -- dite
    let Z':= c!; let T':SpaceP F X G:= (c!∘ Λ); let u:=t •meetVar Z (A! x); let g(j:F.Free):= χ.scale*χ.J (cord F j G u); let Y':= tape (G:=G) (T'+t • x); have he(i:↥(board F X)): cord F i.val G u = Y' i:=by
         have hp:= Bakery.Film.telling J F X Y W U' T' ν χ ha hv (linCash F (t • Z)) h.seat ‹X⊆Y› x hx i; unfold Y'; rw [← hp]; unfold u; rw [_root_.map_smul]; -- simp Function.comp
         rw [Function.comp_apply,(sweet F R v J χ X Y U' t Z h ht x hU hx).1,_root_.map_smul]; rfl
    let X':=board F X; rw [pay, Real.log_prod];
    · change (∑ i:↥(board F X), Real.log (χ.scale*χ.J (Y' i)))=∑ i:F.Free, if hi:i∈board F X then Real.log (g i) else 0
      simp_rw [← he]; rw [← Finset.sum_subtype (board F X) (f:=fun i=>Real.log (g i)) (p:=fun i=> i∈board F X) ?_] -- inspect
      · rw [← sum_subset (Finset.subset_univ (board F X)) ?_]; · refine sum_congr rfl (fun i hi=>?_); rw [dif_pos hi] -- direction
        intro i _ h; rw [dif_neg h]
      intro i;simp
    intro i _; exact (mul_pos ha.scale (ha.pos _ (hx.2 i (Set.mem_univ _)))).ne'
lemma supportP {i:F.Free}(hx:i∉ board F X) : cord F i G (t • meetVar Z (berth F R v J X Y U' Z t x))= cord F i G (t • meetVar Z (berth F R v J X Y U' Z t u)):=by
    rw [map_smul,map_smul]; congr 1; have he(j:G.ColorIndex): (i,j)∉ Set.range Λ:= by rintro ⟨a,h⟩; have ht:i=a.1.val:= congr_arg Prod.fst h.symm; apply hx;rw [ht]; exact a.1.prop
    ext j; change A! x (i,j)=A! u (i,j); unfold berth; rw [Pi.add_apply,Pi.add_apply,inactive _ _ (he j) x,inactive _ _ (he j) u]
lemma roseP (hx:x∈clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U')(hu:u∈clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U'):
     let I':=c! ∘ includeX F X; let H₁(x:X₀):= Real.log (pay χ (tape (I'+t • x)))
     H₁ x-H₁ u=swung F χ (t•meetVar Z (berth F R v J X Y U' Z t x))-swung F χ (t •meetVar Z (berth F R v J X Y U' Z t u)):=by
    intro _ T'; unfold T'; rw [show Real.log _= _ from arcSign F R v J χ X Y U' t Z h ht x hU hp ha hv hx,show Real.log _=_ from arcSign F R v J χ X Y U' t Z h ht u hU hp ha hv hu]; rw [invoice F χ _ ha (ballot F R v J χ X Y U' t Z h ht x hU hp ha hv hx),invoice F χ _ ha (ballot F R v J χ X Y U' t Z h ht u hU hp ha hv hu), ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply sum_congr rfl; intro i hi; unfold signal; simp only [Function.comp_apply]; by_cases hi:i∈ board F X; rw [dif_pos hi,dif_pos hi]; unfold smelt;ring; rw [dif_neg hi,dif_neg hi,supportP F R v J χ X Y U' t Z h ht u x hU hp ha hv hi,sub_self,sub_self]
end YM.MSbar.Jade
