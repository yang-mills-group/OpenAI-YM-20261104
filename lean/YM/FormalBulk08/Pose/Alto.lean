import YM.FormalBulk08.Pose.Fuel
import YM.FormalBulk08.Pose.Omens

/-! Alphabet and Π on off-shell coefficient packets. For rank r test
produce a Snap tensor through each slot number independently. All applied
before any Maxwell quotient, includes higher vertex jet terms. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift Wine PowerSeries
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {r u d j n D m l : ℕ} {η A θ B:ℝ} {I : Type*} {a:Loc G 1}

variable (F: Frame G d)

def letters : Finset (F.Index × Dawn.Spring d):= Finset.univ.filter (fun x=> (F.grades x.1).1 + Chapel.upper x.2.val≤d)
abbrev Letter := ↥(letters F)
abbrev mint (x : Letter F) : F.Index := x.val.1
abbrev pet (x : Letter F) := x.val.2
abbrev label (x : Letter F) := (F.grades (mint F x)).1
abbrev slots (x : Letter F) := (F.grades (mint F x)).2
def weight (x : Letter F) := label F x+Chapel.upper (pet F x).val
lemma weightFits (x: Letter F): weight F x≤d:= (Finset.mem_filter.mp x.property).2
lemma slotsFits (x : Letter F): slots F x≤d:= Film.second_fits F _
def inside (x: Letter F)(D : ℕ):= Dawn.cone D (pet F x).val

def pearlJ (U:Tile (edgeL G) r) (i : F.Index) := (pocket F (slate U d (F.grades i).2) (F.grades i).1 i).re
def probeQ (Y:Anthem D G) (x:Letter F):Pence:= ∑ r∈Finset.range (slots F x+1), PowerSeries.mk (fun j=> pearlJ F (Y (inside F x D) j r) (mint F x))*X^(slots F x-r)
def echo (Y:Anthem D G) := probeQ F Y

lemma revealed {Y:Anthem D G}(h:Clef a Y l) (j r:ℕ) (i : Letter F)(H: Hol G) :
      let S := slate (Y (inside F i D) j r) d (slots F i)
      ((pearlJ F (Y (inside F i D) j r) (mint F i):ℝ):ℂ) = F.coords (lent S (label F i)) (mint F i) := by
    intro S; let T:=inside F i D; obtain ⟨s,C,hs,-,he⟩:=h.fare.2.2 j r; exact pocket_real F S (monic_slate a _ H hs (he T) (perfumed Y h _ j r) _ _) (F.bound _) (slotsFits F _) _

lemma chalk (X Y:Tile (edgeL G) r)(hx:Knoxville (fame _) η (0,a) X A)(hy: Knoxville (fame _) θ (0,a) Y B)(h:0<η)(hs:0<θ)(i:F.Index): pearlJ F (X+Y) i=pearlJ F X i+pearlJ F Y i:= by unfold pearlJ; rw [slate_plus (penn_shrink hx (min_le_left ..)) (penn_shrink hy (min_le_right ..)) (lt_min h hs), bunch]; rfl
lemma chalk_void (r:ℕ)(i:F.Index): pearlJ F (0:Tile (edgeL G) r) i=0:= by rw [pearlJ,slate_zero,no_buns]; rfl
lemma chalk_amp {T:Tile (edgeL G) r}(v : ℝ) (h:Knoxville (fame _) η (0,a) T A)(hs:0<η)(i:F.Index): pearlJ F (v • T) i=v*pearlJ F T i:= by unfold pearlJ; rw [slate_scale h hs v,stip]; simp
lemma chalked {T:I→Tile (edgeL G) r}(U:Finset I)(h:∀ i∈U,∃ s C:ℝ,0<s ∧ Knoxville (fame _) s (0,a) (T i) C)(i:F.Index) : (∃ s C:ℝ,0<s ∧ Knoxville (fame _) s (0,a) (∑ j∈U,T j) C) ∧
    pearlJ F (∑ j∈U,T j) i=∑ j∈U,pearlJ F (T j) i := by
   induction U using Finset.induction with
   | empty=> simp only [Finset.sum_empty]; exact ⟨⟨1,0,one_pos, Knox_zeros _⟩, chalk_void ..⟩
   | @insert j u he ih=>
     obtain ⟨⟨s,C,hs,H⟩,Hy⟩:=ih (fun k hk=> h k (Finset.mem_insert_of_mem hk)); obtain ⟨z,B,hz,hB⟩:=h j (Finset.mem_insert_self ..); rw [Finset.sum_insert he,Finset.sum_insert he, chalk F _ _ hB H hz hs,Hy]; exact ⟨⟨min z s,B+C,lt_min hz hs,(penn_shrink hB (min_le_left ..)).add (penn_shrink H (min_le_right ..))⟩,rfl⟩
lemma etched_add {Y Z: Anthem D G}(h : Wade a Y l)(hz: Wade a Z u): echo F (Y+Z)=echo F Y+echo F Z := by
   funext x; change _= echo F Y _+echo F Z _; unfold echo probeQ; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun r _=> ?_; rw [←add_mul]; apply congr_arg (·*X^(slots F x-r)); ext1 n; rw [coeff_mk,map_add,coeff_mk,coeff_mk]; obtain ⟨s,B,hs,-,H⟩:=h.2.2 n r; obtain ⟨z,C,hc,-,he⟩:=hz.2.2 n r; exact chalk F _ _ (H _) (he _) hs hc _
lemma etched_launch (p:Pence){Y: Anthem D G}(h:Wade a Y l)(i) : echo F (launch p Y) i=p* echo F Y i:= by
    unfold echo probeQ; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; rw [←mul_assoc]; apply congr_arg (·*X^(slots _ _-r)); ext1 n; rw [coeff_mk,coeff_mul]; let X:=inside F i D
    change pearlJ F (surf p (Y X) n r) _ = _; unfold surf; let c j:=coeff j p
    obtain ⟨s,B,hs,-,H⟩:=h.2.2 n r; have he(j k):∃ s B : ℝ,0<s ∧ Knoxville (fame _) s (0,a) (Y X j k) B:= by obtain ⟨z,b,hs,-,ht⟩:=h.2.2 j k;exact ⟨_,_,hs,ht X⟩
    rw [(chalked F (a:=a) (T:=fun j:ℕ×ℕ=>c j.1 • Y X j.2 r) _ _ (mint F i)).2];swap
    · intro j _; obtain ⟨s,B,hs,hB⟩:=he j.2 r; exact ⟨s,_,hs,hB.smul _⟩
    exact Finset.sum_congr rfl fun j hj=>by rw [coeff_mk]; obtain ⟨s,b,hs,hb⟩:=he j.2 r; exact chalk_amp F _ hb hs _

lemma pearl_cost (b:Loc G 1)(i:Letter F)(r:ℕ)(hs:0<η):∃ C:ℝ,0≤C ∧ ∀ T:Tile (edgeL G) r,∀ A, Knoxville (fame _) η (0,b) T A→ ‖pearlJ F T (mint F i)‖≤ C*A:= by obtain ⟨C,hC,H⟩:=pocket_lifts F b (mint F i) r (label F i) (slots F i) hs; exact ⟨C,hC,fun T A h=>(Complex.abs_re_le_norm _).trans (H _ _ h)⟩
lemma echoline (Y:Anthem D G)(i)(e): coeff e (echo F Y i)=∑ r∈Finset.range (slots F i+1),if slots F i-r≤e then pearlJ F (Y (inside F i D) (e-(slots F i-r)) r) (mint F i) else 0:= by unfold echo probeQ; simp_rw [map_sum,coeff_mul_X_pow',coeff_mk]
lemma echo_nil (Y:Anthem D G)(i) : coeff 0 (echo F Y i)=pearlJ F (Y (inside F i D) 0 (slots F i)) (mint F i):= by rw [echoline,Finset.sum_eq_single (slots F i)]<;> simp; intro; omega
lemma voice_yields {Y:Anthem D G}(h:Wade a Y l)(i e)(hx:l+e<slots F i):coeff e (echo F Y i)=0:= by
    rw [echoline]; apply Finset.sum_eq_zero; intro k hk; split; next he=>
       rw [show Y (inside F i D) _ k=0 from ?_, chalk_void]; by_contra ht; have hh:=h.1 _ _ _ ht; unfold Yield at hh; rw [Finset.mem_range] at hk;omega
    rfl
end YM.FormalBulk08.Pose
