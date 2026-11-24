import YM.MS.Orbit.Disc
/-!
# n=2m cube. Inversion fixed-site filter and half-momentum branches.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Function Filter Set Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge} {n:Side}
abbrev periodN (n:Side): Side:= (2:Side)* n
abbrev Kappa : Side:= (2:Side)
lemma k_val : (Kappa).val=2:= rfl
lemma cap_val (n:Side): ( periodN n ).val=2*n.val:= rfl
abbrev τ_frame (n:Side): Ratio Kappa (periodN n):= ⟨ n,rfl ⟩
abbrev α_frame (n:Side): Ratio n (periodN n):= ⟨ Kappa, Nat.mul_comm .. ⟩
abbrev ParSec (n:Side): Site (periodN n) →+ Site Kappa := (α_frame n).residue
abbrev Half : Type:= Site Kappa
abbrev Zone (n:Side):= Site (periodN n)
abbrev Subs (n:Side):= (α_frame n).root
abbrev thin (n:Side) : Half →+ Zone n:= (τ_frame n).root
abbrev thumb (n:Side): Zone n→+ Site n:= (τ_frame n).residue
lemma Liftβ (n:Side)(p:Zone n)(h: ParSec n p=0): p= Subs n ((α_frame n).parent p):= by nth_rw 1 [ ← (α_frame n).unpack_at p]; rw [ show (α_frame n).residue p =0 from h, show Lattice.lift (0: Half)=0 from (by ext; simp [Lattice.lift]; rfl), map_zero, add_zero]; rfl
lemma Liftκ (n:Side)(p:Zone n)(h:thumb n p=0): p=thin n ((τ_frame n).parent p):= by nth_rw 1 [ ← (τ_frame n).unpack_at p]; rw [ show (τ_frame n).residue p=0 from h, show Lattice.lift (0: Site n)=0 from (by ext; simp [Lattice.lift]), map_zero, add_zero]; rfl
lemma downward (p:Zone n): p+p= Subs n (thumb n p):= by
    let F:=periodN n; obtain ⟨x,rfl⟩:= (show Surjective (wrap F) from fun x=> ⟨ _,wrap_lift x ⟩ ) p; rw [show thumb n (wrap F x)= wrap n x from (τ_frame n).residue_wrap _, show Subs n (wrap n x)= _ from (α_frame n).embed_wrap x, ← map_add ]; change wrap F (x+x)=wrap F ( (2:ℕ) • x ); rw [two_smul];
lemma η_anchor (p:Half): thumb n (thin n p)=0:= Ratio.residue_embed ..
lemma pin_zero (p:Site n): ParSec n ( Subs n p )=0:= Ratio.residue_embed ..
lemma z_same (p:Zone n): p= -p ↔ thumb n p=0:= by
    rw [eq_neg_iff_add_eq_zero, downward (n:=n)]; exact ⟨fun h=> (α_frame n).embed_injective (h.trans ( (Subs n).map_zero ).symm), fun h=>h ▸ map_zero _ ⟩
lemma u_car (n:Side)(p:Half): thin n p= -(thin n p):= z_same _|>.mpr (η_anchor p)
lemma curtain {v p:Zone n}(H:v+v+p=0): ParSec n p=0:= by rw [downward] at H; rw [eq_neg_of_add_eq_zero_right H,map_neg,pin_zero,neg_zero]
lemma enter (p u:Zone n)(h:ParSec n p=0): u+u+p=0↔ thumb n u= - ( α_frame n).parent p:= by
    nth_rw 1 [ Liftβ n p h ]; rw [downward, ← map_add]; refine ⟨fun h=>eq_neg_of_add_eq_zero_left ((α_frame n).embed_injective (h.trans ( map_zero (Subs n)|>.symm))), fun hx=>?_ ⟩; rw [hx, neg_add_cancel,map_zero ]
-- char filter
lemma make_coord (p: Half): Coord ( thin n p )=Coord p := by
    change walk ( periodN n ) (Lattice.lift ((τ_frame n).embed p)) = _; rw [(τ_frame n).lift_embed,η_walk]; unfold Coord wrapZ; rw [η_walk]; ext i; rw [at_whole,at_whole]; have hv : (τ_frame n).count=n:=rfl; simp only [ψstep, cap_val,k_val, Pi.smul_apply,nsmul_eq_mul]; obtain hx:= Bloch.side_pos n; push_cast; field_simp
lemma makes (v:Half)(p:Zone n): Bloch.cell (thin n v) p= Bloch.cell v (ParSec n p):= by
   obtain ⟨x,rfl⟩:= (show Surjective (wrap (periodN n)) from fun i=>⟨_,wrap_lift i ⟩) p; rw [ show ParSec n (wrap (periodN n) x)= _ from (α_frame n).residue_wrap x, ← dual_cell, make_coord, dual_cell ]; 
lemma check_total (p:Zone n): ∑ i:Half,Bloch.cell (thin n i) p= if ParSec n p=0 then (16:ℂ) else 0:= by
   simp_rw [makes,Bloch.cell_duality (_:Half) (ParSec n p)]; by_cases he:ParSec n p=0; swap; · rw [if_neg he]; exact Bloch.sum_cell he
   rw [he, if_pos rfl]; simp_rw [ Bloch.cell_duality (0:Half), Bloch.cell_origin ]; simp [Half]
lemma window_roots (p:Zone n)(f:Zone n→ℂ): (∑ i:Zone n, if thumb n i=thumb n p then f i else 0)= ∑ z:Half,f (p+thin n z):= by
   classical
   let V(i: Zone n):= if thumb n i =0 then f (p+i) else 0
   rw [ ← Equiv.sum_comp (Equiv.addLeft p) (fun i=> if thumb n i=thumb n p then f i else (0:ℂ)) ]; have hv(i:Zone n) : thumb n (p+i)= thumb n p↔ thumb n i=0:= by simp only [map_add,add_eq_left]
   simp_rw [ Equiv.coe_addLeft, hv ];
   change ∑ i:Zone n,V i = _; let S:= τ_frame n; rw [← Equiv.sum_comp S.splitSites.symm V,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; have hu (y:Site n): V (S.splitSites.symm (i,y))= if y=0 then f (p+ S.embed i) else 0 := by
        change V ( S.assemble (i,y) )=_; unfold V; rw [ show thumb n ( S.assemble (i,y))= y from S.assemble_res _ ]; split_ifs with h; · subst y; rw [Ratio.assemble, show Lattice.lift (0: Site S.count)=0 from (by ext; simp [Lattice.lift]),map_zero,add_zero]
        rfl
   simp_rw [hu]; rw [Finset.sum_ite_eq']; simp; rfl
end YM.MS.Orbit
