import YM.OPE.Compatible.Emu.Ford
/-!
# Nonlinear chart quadratic hull — arbitrary sector
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter Lattice Laurent Wilson Matrix RG Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open Finset
variable {r s m i b k:ℕ}{n:Side}{G:Gauge} {p:ℤ}
abbrev fringe (r:ℕ)(n:Side): Finset (Edge (Site n)):= (fieldP r).image (Moor · n)
abbrev mesa (r:ℕ)(n:Side): Finset (Edge (Site n)):= (beamP r).image (Moor · n)
lemma Moor_out (x:Edge Cover)(h:Board n (r+2))(hp:x.1∈Lattice.box (r+2)) (he:x∉fieldP r):Moor x n∉fringe r n:=by
       intro ht; obtain ⟨y,hy,hU⟩:= mem_image.mp ht; have hx:y=x:= Prod.ext (berthInj h _ _ (taller (Nat.le_succ _) (arcP (mem_sdiff.mp hy).1).1) hp (congr_arg Prod.fst hU)) (congr_arg (fun e:Edge (Site n)=>e.2) hU); exact he (hx ▸ hy)
noncomputable def curtain (r:ℕ)(U: Config G n): CoverConfig G:=fun e=> if e.1∈Lattice.box (r+2) then U (Moor e n) else 1
lemma cutRead (U:Config G n)(x:Cover)(hx:x∈ Lattice.box (r+1))(p:PlaqAxes): faceValue (curtain r U) (x,p)=faceValue U (wrap n x,p):=by
       rw [circ,circ]
       have ht(y:Cover)(he:y∈ Lattice.box (r+2))(i:Axis): curtain r U (y,i)=U (wrap n y,i):=if_pos he; rw [ht x (taller (Nat.le_succ _) hx),ht (x+step p.val.1) (up _ _ hx).1, ht (x+step p.val.2) (up _ _ hx).1,ht x (taller (Nat.le_succ _) hx)];simp
-- all faces in this box
structure CloudH (r:ℕ)(t f:ℝ)(U:Config G n):Prop where
       art :0 ≤ t
       far :0 ≤ f
       cliff (e:Edge (Site n))(he:e∉fringe r n): G.chord (U e) ≤ t
       fh (L:Face (Per n))(he:pdist L.1 ≤ r+1): G.chord (faceValue U L) ≤ f
namespace CloudH
variable {U:Config G n} {t f:ℝ}
variable (hp:Board n (r+2))(h: CloudH r t f U)
include hp h
lemma flare : Ripe r t f (curtain r U):=by
       refine ⟨h.art,h.far,fun x hx=>?_,fun x hx=>?_⟩; · unfold curtain; split; exact h.cliff _ (Moor_out _ hp (by assumption) hx); rw [chord_one]; exact h.art
       rw [cutRead U x.1 hx x.2]; exact h.fh _ (aery (tip hp (Nat.le_succ _)) hx)
lemma leg (x:Edge Cover)(he:x.1∈Lattice.box (r+2)): G.chord (U (Moor x n)) ≤ soil r t f + maxArr r t f:=by
       rw [← show curtain r U x=U (Moor x n) from if_pos he]; exact (h.flare hp).sumV x
omit hp h
noncomputable abbrev taxC (r:ℕ):ℝ:= soil r 1 1+maxArr r 1 1 +1
lemma taxNL (r:ℕ):1 ≤ taxC r:=by unfold taxC; apply le_add_of_nonneg_left; unfold soil soilV maxArr arrival; positivity
private lemma slope1 (hh:0 ≤ t)(hk:0 ≤ f):soil r t f+maxArr r t f≤taxC r*(t+f):=by
      let A(v:ℝ)(w:ℝ):=arrival (2*r+1) v w; have he:A t f ≤ A (t+f) (t+f):=by unfold A arrival; gcongr <;> linarith
      calc
         _ ≤ soil r (t+f) (t+f)+maxArr r (t+f) (t+f):=by unfold soil soilV; gcongr <;>first| exact he| linarith
         _ = (taxC r-1)*(t+f):=by unfold taxC soil soilV maxArr arrival; ring
         _ ≤ _:=by gcongr; linarith
include hp h
lemma cup (x:Edge (Site n)):G.chord (U x)≤ taxC r*(t+f):=by
       by_cases ht:x∈fringe r n
       · obtain ⟨e,he,rfl⟩:= mem_image.mp ht; exact (h.leg hp e (taller (Nat.le_succ _) (arcP (mem_sdiff.mp he).1).1)).trans (slope1 h.art h.far)
       exact (h.cliff x ht).trans ((le_add_of_nonneg_right h.far).trans (le_mul_of_one_le_left (add_nonneg h.art h.far) (taxNL _)))
end CloudH
lemma fringe_disjoint (h:Board n (r+1)): Disjoint (mesa r n) (fringe r n):=by
       refine Finset.disjoint_left.mpr fun x hx ht=>?_; obtain ⟨j,hj,rfl⟩:= mem_image.mp hx; obtain ⟨k,hk,hH⟩:= mem_image.mp ht; exact (mem_sdiff.mp hk).2 ((peers h (mem_sdiff.mp hk).1 (dockT r hj) hH).symm ▸ hj)
lemma regionH (x:Edge (Site n))(h:Board n (r+1)): x∈ mesa r n ∨ x∈fringe r n↔ x.1∈berth r ∨ dotUp x∈berth r:=by
       constructor
       · rintro (hp|hv); · obtain ⟨j,hJ,rfl⟩:=mem_image.mp hp; exact qual h j (dockT r hJ)
         obtain ⟨j,hJ,rfl⟩:=mem_image.mp hv; exact qual h j (mem_sdiff.mp hJ).1
       intro hh; obtain ⟨j,hj,he⟩:=liftK_delta h x hh; rw [← he]; by_cases hz:j∈beamP r; exacts[Or.inl (mem_image_of_mem _ hz),Or.inr (mem_image_of_mem _ (mem_sdiff.mpr ⟨hj,hz⟩))]
end YM.OPE.Merchant
