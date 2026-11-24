import YM.OPE.Compatible.Soup.Punt
import YM.Work.E04
import YM.Vac.Caps
import YM.OPE.Compatible.Grout.Marl
/-!
# Sparse absolute estimates at all scales
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Set
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal
open Eyrie Push.Mark Cascade Pilot PhysicalNext.Repeat.Aroma Finset
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
local notation "F!"=>Config G n
noncomputable abbrev Toss (U:F!)(b:ℕ):Prop:=∀ i,U i≠1→ pdist i.1 ≤ b∧ pdist (dotUp i) ≤ b
lemma Toss.raise {U:F!}{s:ℕ}(h:Toss U b)(he:b ≤ s): Toss U s:=fun i hi=> ⟨(h i hi).1.trans he,(h i hi).2.trans he⟩
lemma sepK (x y:Site n): pdist x ≤ separation x y + pdist y:=by
       simpa only [separation,sub_zero] using separation_triangle x y 0
lemma berth_eq (n:Side) :berth (n:=n) b=halo b {0}:=by ext i; rw [berthH,halo_spec,show (∃ x∈({0}: Finset (Site n)),separation x i ≤ b)↔separation 0 i ≤ b from by simp,separation_comm, separation,sub_zero]
lemma cardinal_B (n:Side) : (berth (n:=n) b).card ≤ (b+b+1)^4:=by
        rw [berth_eq]; simpa only [Finset.card_singleton,one_mul] using Corona.halo_size ({0}:Finset (Site n)) b
lemma Toss.turn {U:F!} (h:Toss U b)(s:Signed): Toss (pull s 0 U) b:=by
        have hx(y:Site n)(d:Step) (hh:d.read U y ≠1): pdist y≤ b ∧ pdist (y+d.vec)≤ b:=by
             rcases d with ⟨i,th|th⟩; · exact h (y,i) hh
             let z:=y-step i; obtain ⟨hp,H⟩:= h (z,i) (fun H=> hh (show (U (z,i))⁻¹=1 by rw [H,inv_one])); rw [show dotUp (z,i)=y from sub_add_cancel ..] at H; exact ⟨H,by simpa only [Step.vec,↓reduceIte,sub_eq_add_neg,z] using hp⟩
        rintro ⟨x,i⟩ hi; obtain ⟨hA,h'⟩:= hx _ ((posDir i).rotate s) (show Step.read _ U _≠_ from hi); rw[affine,add_zero] at hA h'; rw[Step.vec_rotate,Step.vec_pos,←s.act_add] at h'; exact ⟨by simpa only [pdist_invariant] using hA, (by simpa only [dotUp,pdist_invariant] using h')⟩
lemma Toss.card {U:F!}(h:Toss U b)(s:Support n)(hB:Disjoint s (berth b)): Agrees s U 1:=fun i hi _=> not_not.mp (fun hq=> Finset.disjoint_left.mp hB hi ((berthH _).mpr (h i hq).1))
lemma Toss.face {U:F!} (h:Toss U b)(p:Face (Per n))(he:faceValue U p≠1):p.1∈berth (b+2):=by
        by_contra hp; apply he
        have hv:Disjoint (RG.touched p) (berth b):=Finset.disjoint_left.mpr fun j hj hT=> hp ((berthH _).mpr ((sepK p.1 j).trans ((Nat.add_le_add (Work.E01.sep_touched p j hj) ((berthH _).mp hT)).trans_eq (by omega))))
        have hh: faceValue U p=faceValue 1 p:=travel_local _ _ U 1 (fun e he hm=> h.card _ hv e (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hm)); rw [hh]; simp [faceValue,square]
lemma Toss.sparks {U:F!}(h:Toss U b)(p:Slot)(x:Site n)(hp:p.atSite U x≠0):wrap n p.offset+x∈ berth (b+2):=by
        let V:= faceValue U (wrap n p.offset+x,p.plaq); apply h.face (wrap n p.offset+x,p.plaq); intro hh; apply hp
        have he : faceValue (expandAt x U) (p.offset,p.plaq)=V:=travel_at ..; unfold Slot.atSite Slot.eval; rw [he,show V=1 from hh,G.curvature_unit, map_zero]
lemma Toss.seeds {U:F!}(h:Toss U b)(P:Atom G k)(x:Site n)(i:Fin k) (hp:P.unmasked U x≠0): wrap n (P.leg i).offset+x∈ berth (b+2):=by
        refine h.sparks (P.leg i) x (fun hh=> hp ?_); unfold Atom.unmasked Atom.poly; refine Finset.sum_eq_zero fun j _=>?_ ; rw [prod_eq_zero (mem_univ i),mul_zero];change (P.leg i).atSite U x (j i)=0; rw [hh];rfl
-- weight footing.Alias free
noncomputable def Shoal (b:ℕ):ℝ:= (↑(((b+2)+(b+2)+1)^4:ℕ):ℝ)
lemma Shoal.one (b:ℕ):1 ≤ Shoal b:=by unfold Shoal; norm_cast; exact Nat.one_le_pow _ _ (by omega)
lemma shore (p:Site n)(g: Site n→ℝ) (c:ℝ)(hp:∀ i, ‖g i‖ ≤ c) (h:∀ i,g i≠0 → p+i∈ berth (b+2)): ∑ i, ‖g i‖ ≤ Shoal b*c:=by
        let X:= (berth (n:=n) (b+2)).image (fun i=>i-p); have hc: 0 ≤ c:= (norm_nonneg (g p)).trans (hp p); rw [← Finset.sum_subset (s₁:=X) (Finset.subset_univ _) (fun x _ hx=>?_)]
        · exact (sum_le_sum fun i _=> hp i).trans (by rw[sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hc; exact Nat.cast_le.mpr (card_image_le (s:=berth (n:=n) (b+2)) (f:=fun i=>i-p) |>.trans (cardinal_B n (b:=b+2))))
        apply norm_eq_zero.mpr; by_contra hY; exact hx (mem_image.mpr ⟨p+x,h x hY,add_sub_cancel_left ..⟩)
end YM.OPE.Merchant.Aloof
