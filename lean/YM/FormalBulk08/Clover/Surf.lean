import YM.FormalBulk08.Clover.Sweet
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Clover
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{E m n l e r j t d D R:ℕ}{X I:Type} {τ:Time X}{σ η δ g:X→ℝ}
variable {Z:Frame G d}{Y W:X→Plaza Z D}{T S:X→Tilework Z}{o:Loc G 1}{b b':X→ Letter Z→ℝ}

def itinerary (Z:Frame G d)(x:Letter Z)(e r:ℕ)(y:Letter Z)(i j:ℕ):Prop:= i<e ∨ i=e ∧ (slots Z y<slots Z x ∨ slots Z y = slots Z x ∧ (r<j ∨ r=j ∧ weight Z x< Pose.weight Z y))
lemma offhand (x: Letter Z) (h:precede e r j t) : itinerary Z x e r x j t:= by unfold itinerary precede at *;omega
lemma ord_only {x y:Letter Z} (h:slots Z y<slots Z x ∨ slots Z y=slots Z x ∧ Pose.weight Z x< Pose.weight Z y) : itinerary Z x e r y e r:=by unfold itinerary;omega
lemma chalk_less (F:Frame G d){T Y: Anthem D G}(x:Letter F)(h:Wade o Y l)(ht:Wade o T l): echo F (T-Y) x= echo F T x - echo F Y x:= by
    have he:= etched_add F (ht.sub h) h; rw [sub_add_cancel] at he; exact eq_sub_of_add_eq (congr_fun he.symm x)
lemma rent_city (x y:Letter Z)(w:∀ i:X,Court o Z (Y i)) (e:ℕ) : Faint τ (fun _ : X=>1) (fun i=>coeff e (echo Z (Y i x) y)):= by
    simp_rw [Court.city (w _)]; let p:ℝ:=coeff e (if y=x then (1:Pence) else 0); exact ⟨fun _=>|p|,soft_coin _ _,fun _=>abs_nonneg _,fun _=> (by rw [mul_one])⟩
lemma rent_gap (w:∀ i:X,Court o Z (Y i))(h:∀ i:X,Court o Z (W i))(x y:Letter Z)(e): Faint τ g (fun i=> coeff e (echo Z ((Y i x)-(W i x)) y)) := by
    rw [show (fun i=>coeff e (echo Z _ y))=0 from funext fun i=> by rw [chalk_less Z y (h i|>.officers x).fare (w i|>.officers x).fare,Court.city (h i), Court.city (w i),sub_self,map_zero]; rfl]; exact faint_zero ..

-- book of coefficient at one column x,e rank;
-- repeated term removed
abbrev paidSet {Z:Frame G d}(_x:Letter Z)(e:ℕ): Finset (Letter Z × (ℕ×ℕ)):= Finset.univ ×ˢ Finset.antidiagonal e
def tickets (Z:Frame G d)(Y: Plaza Z D)(T:Tilework Z)(x:Letter Z)(p:Studio D)(r:ℕ)(i:Letter Z × (ℕ×ℕ)): Tile (edgeL G) r:= coeff i.2.1 (T i.1 x) • Y i.1 p i.2.2 r

def track (Z:Frame G d)(Y:Plaza Z D)(T:Tilework Z)(x:Letter Z)(p:Studio D)(e r:ℕ) : Tile (edgeL G) r:=∑ i∈(paidSet x e).erase (x,0,e), Clover.tickets Z Y T x p r i
lemma employee (Z:Frame G d)(Y:Plaza Z D)(T:Tilework Z)(x:Letter Z)(p:Studio D)(e r:ℕ) : larch Y T x p e r=coeff 0 (T x x) • Y x p e r+track Z Y T x p e r:= by
    change _= Clover.tickets Z Y T x p r (x,0,e)+ _; unfold Clover.track; rw [Finset.add_sum_erase (paidSet x e) _ (by simp [paidSet]),paidSet,Finset.sum_product]; simp only [larch,Finset.sum_apply]; rfl
lemma seat_void (x y:Letter Z)(h: slots Z y+j<r)(T:Plaza Z D)(P:Tilework Z)(ht:Court o Z T)(p:Studio D): tickets Z T P x p r (y,(n,j))=0:= by
    unfold Clover.tickets; rw [show T y p j r=0 from Classical.byContradiction fun hu=> (not_lt.mpr ((ht.officers y).fare.1 p j r hu)) h, smul_zero]
lemma purchased (x:Letter Z)(e r:ℕ)(h:∀ i,Colfax (slots Z) (Pose.weight Z) (T i) (b i))(hs:∀ i,Colfax (slots Z) (Pose.weight Z) (S i) (b' i))(hv:∀ i,Court o Z (Y i))(ht:∀ i,Court o Z (W i))(hp:∀ y j, j<e ∨ j=e ∧ r≤slots Z y → Pact τ δ (fun i=>coeff j (T i y x)) (fun i=>coeff j (S i y x)))(hA:∀ y j k,itinerary Z x e r y j k→ Brass τ o η δ g (fun i p=> Y i y p j k) (fun i p=> W i y p j k)) : Brass τ o η δ g (fun i p=>track Z (Y i) (T i) x p e r) (fun i p=>track Z (W i) (S i) x p e r):= by
    unfold Brass Clover.track; apply matched_sums _; rintro ⟨y,t,s⟩ hw
    obtain ⟨hl,hr⟩:=Finset.mem_erase.mp hw; have hb:t+s=e:=Finset.mem_antidiagonal.mp (Finset.mem_product.mp hr).2
    by_cases hx: slots Z y + s< r
    · simp_rw [seat_void x y hx _ _ (hv _), seat_void x y hx _ _ (ht _)]; exact mates_void ..
    have he:= hp y t (by omega)
    by_cases hu:t=0
    · subst t; have hg : s=e:=by omega
      have hh:x≠y:= fun he=>hl (by rw [he,hg]); subst s
      by_cases hY: itinerary Z x e r y e r
      · exact (Matched.amp (hA y e r hY) he)
      have ht i:coeff 0 (T i y x)=0:= Classical.byContradiction fun z=> hY (ord_only ((h i).peers y x z (Ne.symm hh)))
      have hh i:coeff 0 (S i y x)=0:= Classical.byContradiction fun z=>hY (ord_only ((hs i).peers y x z (Ne.symm hh)))
      simp only [Clover.tickets,ht,hh,zero_smul]; exact mates_void ..
    exact Matched.amp (hA y s r (Or.inl (by omega))) he
end YM.FormalBulk08.Clover
