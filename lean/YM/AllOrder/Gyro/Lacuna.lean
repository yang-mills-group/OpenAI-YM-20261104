import YM.AllOrder.Gyro.Wave
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro
open Function Filter Lattice RG Wilson Push Push.AbsoluteSums Precision AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{p:BudgetPoint}(d:RegularAddress n){f:Config G n→ℝ}(g:G.Simple)(H:p.Regular d.support f) (x y:Site n) (b:PlaqAxes)
section geos
variable (w B:ℕ)(u:Support n)(o:Site n) (d' : Seat n) (hn:20<n.val)
lemma highest : |coord x y b.val.1| ≤ (n.val:ℝ):= by
 refine (small_coord x y _).trans (Nat.cast_le.mpr ((show separation y x ≤ n.val from Finset.sup_le (f:=fun i=>(lift (y-x) i).natAbs) fun (i:Axis) (_:i∈Finset.univ)=>?_))); change _ ≤ n.val; have hh:=(lift_centers (y-x) i); omega
include hn
lemma transport_nonwrap (h:d.site=o) (h₁:Nonwrapping d.support d.site) : Nonwrapping (expand d) o := by
    subst o; intro x hx; rcases Finset.mem_union.mp hx with hx|hx; exact h₁ x hx
--
    obtain ⟨y,hy,h⟩:= halo_spec.mp hx; rw [Finset.mem_singleton.mp hy,separation_comm] at h; omega
-- global min, avoid choosing near rect stencil and estimating geometry upper by path balls with different size (could lose true rate). branch supplies call-independent.
def Toll (n:Side)(B k:ℕ) := ∃ d:RegularAddress n, ¬ Nonwrapping d.support d.site ∧ coverNumber B d.support = k
include hn
lemma warp {B:ℕ} : ∃ k:ℕ,Toll n B k:= by
 let s := (n.val/3:ℕ); let x : Cover := fun _=> s
 have hv: lift (wrap n x)=x:= lift_eq_iff.mpr ⟨rfl,fun i=>by unfold x s; omega⟩
 let u : RegularAddress n:= ⟨0, Finset.univ,Finset.mem_univ 0⟩
 refine ⟨coverNumber B u.support, u,fun he=>?_,rfl⟩
 have hS : 10*separation (wrap n x) 0 < n.val:= he _ (mem_univ (wrap n x)); have he:= component_le (wrap n x) 0; rw [hv] at he; change Int.natAbs (s:ℤ) ≤ pdist _ at he; rw [separation,sub_zero] at hS; have h : s=(n.val/3:ℕ) :=rfl; omega
variable (n) in
def pitch (B:ℕ):ℕ:= if h:20<n.val then Nat.find (warp (n:=n) (B:=B) h) else 0
structure Tooth (n:Side) (B:ℕ) extends RegularAddress n where
 excess : ¬Nonwrapping support site
 economical : coverNumber B support=pitch n B
lemma settle : Nonempty (Tooth n B):= by rw [show B=B from rfl]; obtain ⟨d,h,H⟩:= (Nat.find_spec (warp (n:=n) (B:=B) hn)); exact ⟨⟨d,h,(by rw [H,pitch,dif_pos hn])⟩⟩
-- W/O Pin site 0; distribute via Seat.action *root moves* not formula Seat.seat rooted at 0 unless move.
lemma adjudicate {d:RegularAddress n} (h: ¬ Nonwrapping (expand d) d.site) : pitch n B ≤ coverNumber B d.support:= by rw [pitch,dif_pos hn]; exact Nat.find_min' (warp hn) ⟨d,fun he=> h (transport_nonwrap d d.site hn rfl he),rfl⟩
-- lower rough estimate suitable only polynomial expenditure through Hphi
lemma wat (d:RegularAddress n)(h: ¬ Nonwrapping d.support d.site) : n.val ≤ 10*(coverNumber B d.support*(4*B+2) + 2*B):= by
 obtain ⟨x,hx⟩ := Classical.not_forall.mp (show ¬∀ x∈d.support,10*separation x d.site<n.val from h); obtain ⟨hv,hy⟩:= not_forall.mp hx
 refine (Nat.not_lt.mp hy).trans (Nat.mul_le_mul_left _ (Corona.extent d.support B hv d.anchor))
lemma wake : n.val ≤ 10*(pitch n B*(4*B+2) +2*B) := by obtain ⟨u⟩:= settle B hn; rw [← u.economical]; exact wat B hn u.toRegularAddress u.excess
end geos
end YM.AllOrder.Gyro
