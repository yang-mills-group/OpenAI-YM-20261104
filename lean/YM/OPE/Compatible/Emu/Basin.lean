import YM.OPE.Compatible.Kash.Lift
/-!
# Occupied chamber on a large torus

Proof ingredients for estimating the X-state Projection. External configurations
are independent of this chamber; its size will NOT grow with the physical
period or $β$ (it can grow with the requested horizon!). Lace will be the
dependent variables, with one leg kept still for each covered vertex.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open Finset
variable {r s m i:ℕ} {n:Side}
variable {V:Type*}
local notation "EL" I=> Edge I
abbrev dotUp {R:Type*}[AddCommGroup R][One R](e:Edge (Four R)):=e.1+step e.2
lemma taller (h:r ≤ s){x:Cover}(hx:x∈Lattice.box r):x∈Lattice.box s:=by
   obtain ⟨hz,hx⟩:= Lattice.box_test.mp hx; refine Lattice.box_test.mpr ⟨fun i=>?_,fun i=>?_⟩; · specialize hz i; omega
   specialize hx i; omega
lemma lift_le (x:Site n):pdist x ≤ r ↔ lift x∈Lattice.box r:=by
    rw [pdist,Finset.sup_le_iff,box_test]; constructor
    · intro h; refine ⟨?_,?_⟩ <;> intro i <;> specialize h i (mem_univ i)<;> omega
    rintro ⟨ha,h⟩ i _; specialize ha i; specialize h i; omega
-- HP needed before caller for injection
abbrev Board (n:Side) (r:ℕ):Prop:=2*r<n.val
lemma tip (h:Board n r)(hk:s ≤ r):Board n s:=Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hk) h
lemma level (h:Board n r){x:Cover}(hx:x∈Lattice.box r):lift (wrap n x)=x:=by
      refine lift_eq_iff.mpr ⟨rfl,fun i=>?_ ⟩; unfold Board at h; obtain ⟨hv,ht⟩:=box_test.mp hx; specialize hv i; specialize ht i; omega
lemma aery (h:Board n r){x:Cover}(hx:x∈Lattice.box r):pdist (wrap n x) ≤ r:= (lift_le _).mpr (by rw [level h hx]; exact hx)
noncomputable def berth (r:ℕ):= (@univ (Site n) _).filter (fun x=>pdist x ≤ r)
lemma berthH (x:Site n): x∈berth r ↔ pdist x≤r:= mem_filter.trans (and_iff_right (mem_univ _))
lemma baud (h:Board n r):berth (n:=n) r=(Lattice.box r).image (wrap n):=by ext x; rw [berthH,lift_le, mem_image]; exact ⟨fun hi=> ⟨_,hi,wrap_lift _⟩,fun ⟨y,h,r⟩=>lift_le x |>.mp (r ▸ aery (by assumption) h)⟩
lemma up (x:Cover)(a:Axis)(h:x∈Lattice.box r): x+step a∈Lattice.box (r+1) ∧ x-step a∈Lattice.box (r+1):=by
      obtain ⟨hv,hh⟩:=box_test.mp h; simp only [box_test]; constructor <;> constructor <;> intro i <;> specialize hv i<;>specialize hh i<;>simp only[Pi.add_apply,Pi.sub_apply,step_apply] <;> split_ifs <;> omega
lemma boulder (a:Axis) (x:Site n): pdist (x-step a) ≤ pdist x+1∧ pdist (x+step a) ≤ pdist x+1:=by
     have ht:=pdist_step (n:=n) a; rw[sub_eq_add_neg]; have he: pdist (- step a:Site n) ≤1:= (pdist_neg _).trans_le ht; exact ⟨(pdist_triangle ..).trans (by gcongr),(pdist_triangle ..).trans (by gcongr)⟩
noncomputable abbrev Moor (e:Edge Cover)(n:Side): EL (Site n):= (wrap n e.1,e.2)
lemma pier (x:Edge Cover): wrap n (dotUp x)=dotUp (Moor x n):=by simp [dotUp]
noncomputable abbrev Delta (r:ℕ):Finset (Edge Cover):= ((Lattice.box (r+1)) ×ˢ (Finset.univ:Finset Axis)).filter (fun e=> e.1∈ Lattice.box r ∨ dotUp e ∈ Lattice.box r)
abbrev knot (x:Cover)(i:Axis): Edge Cover := (x,i)
lemma deck (e:Edge Cover): e∈Delta r ↔ e.1∈ Lattice.box r ∨ dotUp e∈Lattice.box r:= by
       rw [Delta,mem_filter]; refine and_iff_right_of_imp fun h=> mem_product.mpr ⟨?_,mem_univ _⟩; rcases h with h|h; exact taller (Nat.le_succ _) h; exact (add_sub_cancel_right e.1 _) ▸ (up _ e.2 h).2
lemma arcP {e:Edge Cover}(h:e∈Delta r): e.1∈Lattice.box (r+1)∧dotUp e∈Lattice.box (r+1):=by
        rcases (deck e).mp h with h|h
        · exact ⟨taller (Nat.le_succ _) h, (up _ _ h).1⟩
        exact ⟨(add_sub_cancel_right e.1 _) ▸ (up _ _ h).2,taller (Nat.le_succ _) h⟩
lemma qual (hx:Board n (r+1)) (x:Edge Cover)(h:x∈Delta r): (Moor x n).1 ∈berth r∨ dotUp (Moor x n) ∈ berth r:=by
    rw [baud (tip hx (Nat.le_succ _)),←pier]; rcases (deck x).mp h with h|h; exacts [Or.inl (mem_image_of_mem _ h),Or.inr (mem_image_of_mem _ h)]
lemma liftK_delta (hx:Board n (r+1)) (x:EL (Site n))(he:x.1∈berth r ∨ dotUp x ∈ berth r): ∃ y∈Delta r,Moor y n=x:=by
       rcases he with h|h
       · rw [baud (tip hx (Nat.le_succ _))] at h; obtain ⟨y,hy,hh⟩:= mem_image.mp h; exact ⟨(y,x.2),deck ..|>.mpr (Or.inl hy),Prod.ext hh rfl⟩
       rw [baud (tip hx (Nat.le_succ _))] at h; obtain ⟨y,hy,hh⟩:= mem_image.mp h; refine ⟨(y-step x.2,x.2),(deck _).mpr (Or.inr (by simp [dotUp,hy])),Prod.ext ?_ rfl⟩
       change wrap n (y-_)=_; rw [map_sub,wrap_step,hh, dotUp, add_sub_cancel_right]
lemma berthInj (h:Board n r) (x y:Cover)(hx:x∈Lattice.box r)(hy:y∈Lattice.box r)(he:wrap n x=wrap n y):x=y:= (level h hx).symm.trans ((congr_arg lift he).trans (level h hy))
lemma peers {x y:Edge Cover}(h:Board n (r+1))(hx:x∈Delta r)(hy:y∈Delta r)(he:Moor x n=Moor y n):x=y:= Prod.ext (berthInj h x.1 y.1 (arcP hx).1 (arcP hy).1 (congr_arg Prod.fst he)) (congr_arg (fun x:EL (Site n) => x.2) he)
-- T/F partitions.Vertical chosen arbitrary
abbrev perch :Axis:=0
noncomputable def beamP (r:ℕ):= (Lattice.box r).image fun x=>(knot x perch)
lemma beamH (x:Edge Cover): x∈beamP r↔x.2=perch∧x.1∈Lattice.box r:=by
       rw [beamP,mem_image]; constructor
       · rintro ⟨x,h,rfl⟩; exact ⟨rfl,h⟩
       rintro ⟨h,hh⟩; exact ⟨x.1,hh,Prod.ext rfl h.symm⟩
lemma dockT (r:ℕ):beamP r⊆Delta r:= fun x h=> deck ..|>.mpr (Or.inl ((beamH x).mp h|>.2))
noncomputable abbrev fieldP (r:ℕ):=Delta r\beamP r
lemma fieldH (x:Edge Cover):x∈fieldP r↔ x∈Delta r∧x∉beamP r:=mem_sdiff
end YM.OPE.Merchant
