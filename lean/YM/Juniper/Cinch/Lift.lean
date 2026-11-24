import YM.Juniper.Cinch.Ease
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
open Quotes Finset Matrix Further.LogJets Pressure
set_option quotPrecheck false
variable (P:BudgetPoint)
section turn
variable {p₀ q:BudgetPoint} {k:ℕ}{n:Side}
local notation "N"=> n.val
lemma beyond (hn:20<n.val): ∃ x:Site n, n.val≤ 10 * separation x 0:= by
    let a:= N/2; let p(i:Axis):ℤ:=a; let x:= wrap n p
    have hp:lift x=p:= lift_eq_iff.mpr ⟨rfl,fun i=>by unfold p a; omega⟩; refine ⟨x,?_⟩; have hh:(lift x 0).natAbs ≤ separation x 0:= by rw [separation,sub_zero]; exact component_le x 0
    rw [hp] at hh; unfold p a at hh; omega

lemma momentumP {i:RegularAddress c}(hn:20<c.val) : Nonwrapping (expand i) i.site ↔ Nonwrapping i.support i.site:= by
   refine ⟨fun h x hx=> h x (Finset.mem_union_left _ hx),fun h x hx=> ?_⟩
   obtain h'|hv:= Finset.mem_union.mp hx; exact h _ h'
   obtain ⟨y,hy,hx⟩:= halo_spec.mp hv; rw [Finset.mem_singleton.mp hy,Lattice.separation_comm] at hx; omega
abbrev Worth (P:BudgetPoint)(n:Side)(u:ℕ) := ∃ (p:RegularAddress n),¬ Nonwrapping p.support p.site ∧ coverNumber P.B p.support=u
lemma escrow (hn:20<n.val): ∃ u, Worth P n u:=by
   obtain ⟨x,hx⟩:= beyond (n:=n) hn
   let e : RegularAddress n:= ⟨0,univ,mem_univ _⟩; refine ⟨_,e,fun h=> hx.not_gt ?_,rfl⟩; exact h x (mem_univ _)
def turnB (p:BudgetPoint)(n:Side):ℕ:= if h: 20<n.val then Nat.find (escrow p h) else 0
lemma turn_be (hn:20<c.val) (i:RegularAddress c) (hi:¬ Nonwrapping (expand i) i.site): turnB P c ≤ coverNumber P.B i.support:=by rw [turnB,dif_pos hn]; exact Nat.find_min' (escrow P hn) ⟨i,fun h=> hi ((momentumP hn).2 h),rfl⟩
-- realize translated support clover-used aperture
structure Pylon (c:Side) where
    corner : Support c
    az : (0:Site c) ∈ corner
    high : ¬ Nonwrapping corner 0
    clap : halo 2 {0} ⊆ corner
    short : coverNumber P.B corner ≤ turnB P c +81
lemma slate (hn:20<c.val)(hw:2 ≤ P.B): Nonempty (Pylon P c):= by
   obtain ⟨i,h,e⟩:= Nat.find_spec (escrow P hn); let d:= expand i; let Q:Seat c := (1,-i.site); let X₁:= Q.spread d
   have he:Lattice.affine Q.1 Q.2 i.site=0:= by unfold Q Lattice.affine; simp
   have hc:halo 2 {(0:Site c)} ⊆ X₁:= by rw [← (show Push.Local.turnSites Q.1 Q.2 i.site=0 from he),← Finset.image_singleton, Push.Local.halo_map _ (Push.Local.turn_sep _ _)]; exact Finset.image_subset_image Finset.subset_union_right
   refine ⟨⟨X₁,hc (halo_subset 2 _ (mem_singleton_self _)),?_, hc,?_⟩⟩
   · rw [← he]; exact fun h' => h ((momentumP hn).mp ((spin_wrap Q.1 Q.2 _).1 h'))
   unfold X₁; rw [Q.visit_count,turnB,dif_pos hn,← e]; exact Geo.enlarge _ _ hw
lemma rising (hn:20<c.val) : (c.val:ℝ) ≤ 10*((4*P.B+2)*(turnB P c:ℝ) +2*P.B):= by
   obtain ⟨i,h,he⟩:= Nat.find_spec (escrow P hn); unfold Nonwrapping at h; push Not at h; obtain ⟨x,hx,hV⟩:=h; rw [turnB,dif_pos hn,← he]; rw [mul_comm (4*(P.B:ℝ)+2)]; exact_mod_cast hV.trans (Nat.mul_le_mul_left 10 (Corona.extent _ P.B hx i.anchor))
end turn
end YM.Juniper.Cinch
