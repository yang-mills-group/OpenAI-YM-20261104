import YM.AllOrder.Till.Foliage
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quadratic
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Placement
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
open Work.F03 AnalyticBridge VerifiedReset Next.Scheduling
-- affine at identity link using native color curvature probe. all Good results use p.threshold.
def yawn (b:Atom G k)(o:Site n) (U:Config G n):= b.unmasked U o
lemma loop_root (b:Atom G k)(hk:0<k)(o:Site n) : yawn b o (1:Config G n)=0:= by
 letI : Nonempty (Fin k):= ⟨⟨0,hk⟩⟩; simp [yawn,Atom.unmasked,Atom.poly,atSite_path,WilsonStartup.face_one,G.curvature_unit,zero_pow (Nat.ne_of_gt hk)]
local notation "n₀"=> (𝓝[≠] (0:ℝ))
abbrev court (x:Site n)(w:ℕ):= halo w {x}
variable (u:LinearJet G)(o:Site n)(hn:Nonwrapping (court o w) o)(hv:4≤n.val)
lemma birth (b:T)(h:b.length≤w)(o:Site n): b.footprint o⊆court o w:= by
 rintro x hx; obtain ⟨y,hξ,rfl⟩:= mem_image.mp hx; obtain hq|hq:= mem_insert.mp hξ; · subst y; simpa only [map_zero,zero_add] using halo_subset w {o} (mem_singleton_self o)
 obtain ⟨i,hi,hz⟩:= mem_biUnion.mp hq; refine halo_spec.mpr ⟨o,mem_singleton_self _, ?_⟩; rw [separation_comm]; exact (VerifiedReset.slot_length (b.leg i) o (mem_image_of_mem _ hz)).trans ((Finset.single_le_sum («f»:=fun i=>(b.leg i).length) (fun _ _=>Nat.zero_le _) hi).trans h)
lemma unit_price (b:T)(p:BudgetPoint)(o:Site n)(h:b.Invariant)(hc:b.length≤w): p.Regular (court o w) (yawn b o) ∧ p.supBounds o (court o w) (yawn b o) (Wages.price p b):= ⟨reg_larger (Extra.Iteration.Derivs.canonical_regular b o p h) (birth b hc o),sup_larger (Wages.total p b o) (birth b hc o)⟩
local notation "f"=> (u.field o)
include hn hv
def affinity (b:T)(u:LinearJet G):= b.poly fun i=> u.positive (b.leg i).plaq
lemma siege (b:T)(h:b.length≤w): Tendsto (fun t:ℝ=> yawn b o (line (u.field o) t)/t^k) n₀ (𝓝 (affinity b u)):= by
 have he (i:Fin k): Tendsto (fun t:ℝ=> t⁻¹ • (b.leg i).atSite (line f t) o) n₀ (𝓝 (u.positive (b.leg i).plaq)):= by
    let x:= (slotFace (b.leg i) o).1; refine slot_affine_limit _ _ _ (hn x (halo_spec.mpr ⟨o,mem_singleton_self _,?_⟩)) hv; rw [separation_comm]; exact (VerifiedReset.slot_length (b.leg i) o (offset_inside ..)).trans ((Finset.single_le_sum («f»:=fun j=>(b.leg j).length) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans h)
 let F (t:ℝ)(i:Fin k):=t⁻¹ • (b.leg i).atSite (line (u.field o) t) o; apply (((show Continuous b.poly by unfold Atom.poly; fun_prop).tendsto _).comp (show Tendsto F n₀ (𝓝 fun i=> u.positive (b.leg i).plaq) from tendsto_pi_nhds.mpr he)).congr; intro t; unfold yawn Atom.unmasked; simp only [Function.comp_apply,F,Atom.poly, Finset.sum_div,PiLp.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]; apply Finset.sum_congr rfl; intro i _; simp only [Finset.prod_const,card_univ,Fintype.card_fin,inv_pow]; ring
lemma more (b:T)(h:b.length ≤ w)(ht:2<k): Tendsto (fun t:ℝ=> yawn b o (line (u.field o) t)/t^2) n₀ (𝓝 0):= by
 let v:= affinity b u; refine (show Tendsto (fun t:ℝ=> (yawn b o (line (u.field o) t)/t^k)*t^(k-2)) n₀ (𝓝 0) from (by simpa only [id_eq,zero_pow (by omega : k-2≠0),mul_zero] using (siege u o hn hv b h).mul (((tendsto_id (x:=𝓝 (0:ℝ))).mono_left nhdsWithin_le_nhds).pow (k-2)))).congr' ?_; filter_upwards [show ∀ᶠ x:ℝ in n₀,x≠0 from self_mem_nhdsWithin] with x h; rw [show x^k=x^2*x^(k-2) by rw [← pow_add]; congr 1; omega]; field_simp
omit hn hv
-- partial aggregate
section sum
variable {ι:Type}{Y:Support n}{o:Site n}(p:BudgetPoint)
lemma good_sum {F:ι → Config G n→ℝ}{C:ι→ℝ}(s:Finset ι)(h:∀ i∈s,p.Regular Y (F i)∧ p.supBounds o Y (F i) (C i)): p.Regular Y (fun x=>∑ i∈s,F i x) ∧ p.supBounds o Y (fun x=>∑ i∈s,F i x) (∑ i∈s,C i):= by
 rw [show (fun x=> ∑ i∈s,F i x)=(∑ i∈s,F i) from funext fun x=> (Finset.sum_apply ..).symm]; exact ⟨PhysicalNext.Repeat.Meadow.regularA s (fun i hi=> (h i hi).1), PhysicalNext.Repeat.Trio.sup_S (B:=p) _ _ _ _ _ (fun i hi=> (h i hi).1) (fun i hi=>(h i hi).2)⟩ -- universe
end sum
end YM.AllOrder.Till
