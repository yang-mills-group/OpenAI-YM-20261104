import YM.WilsonCoeffUV.Stable.Project
/-! # Uniformities via finite masks and supply compiler. Elementary power shelves.-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {I J V U E:Type*}{r h D l j e k a m u N:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B δ:ℝ}
-- elementary supremum over fixed shape budgets, even over inaccessible tuples
lemma gazette (G:Type*)(s:Finset I)(P:I→G→ℕ→ℝ→Prop)(h:∀ i∈s,∃ d:ℕ,∀ j:G,∃ C,0 ≤ C∧P i j d C)(q:∀ i∈s,∀ j,∀ d e:ℕ,∀ a b, d≤ e→0≤a→a≤ b→P i j d a→P i j e b): ∃ d:ℕ,∀ j,∃ C:ℝ,0≤C∧∀ i∈s,P i j d C:=by
  classical
  induction s using Finset.induction_on with
  | empty=> exact ⟨0,fun i=> ⟨0,le_rfl,by simp⟩⟩
  | @insert i s p ih=>
      have hp:i∈insert i s:= Finset.mem_insert_self ..; obtain ⟨d,H⟩:= h i hp; obtain ⟨e,G⟩:=ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)) (fun i hi=>q i (Finset.mem_insert_of_mem hi))
      refine ⟨max d e, fun j=>?_⟩; obtain ⟨A,hA,h⟩:=H j; obtain ⟨B,hB,h'⟩:= G j; refine ⟨A+B,add_nonneg hA hB,fun i hi=>?_⟩; rcases Finset.mem_insert.mp hi with e|g; subst i; exact q i hp j _ _ _ _ (le_max_left ..) hA (le_add_of_nonneg_right hB) h
      exact q i hi j _ _ _ _ (le_max_right ..) hB (le_add_of_nonneg_left hA) (h' i g)
lemma logStep {a b x y:ℝ}(p:j≤k)(h:0≤a)(hi:a≤b)(hx:1≤x)(hy:0≤y): a*x^j*y ≤ b*x^k*y:=mul_le_mul_of_nonneg_right (mul_le_mul hi (pow_le_pow_right₀ hx p) (by positivity) (h.trans hi)) hy
-- def Strip. Telescope. Tier gear independent operations

def Orchard (I:Gear G)(P:Stand I)(h k:ℕ)(Y:Single G D) : Single G D:=gradeH I.patch h k • fanfare I P k Y
lemma Air.steeps (p:lowerGrade m j e k)(h v:ℕ): Air G e k D u j (fun I w=> Orchard I w.P.P h v w.Y m j) (fun I w=> Orchard I w.P.Q h v w.Z m j):=by
    simp only [Orchard,Pi.smul_apply]; exact Fallow.st (Bank.Slate.one (P:=fun i: Gear G=> gradeH i.patch h v) (Meter.air G e k D u).shine) (Air.higher p v) (Meter.air G e k D u)
lemma uniform_air (e k u r h v D:ℕ)(G:Gauge) : ∃ d:ℕ,∀ I: Gear G,∃ C:ℝ,0≤C∧∀ P:SumT I e k D u,∀ i j, lowerGrade i j e k→j≤r → YieldP 0 P.η u (C*P.x^d*P.fund) P.σ (Orchard I P.P.P h v P.Y i j) (Orchard I P.P.Q h v P.Z i j):=by
   classical
   let S:= ((Finset.range (e+1))×ˢ(Finset.range (r+1))).filter (fun i=> lowerGrade i.1 i.2 e k); let R (x:ℕ×ℕ)(I:Gear G)(d:ℕ)(C:ℝ):=∀ P:SumT I e k D u,YieldP 0 P.η u (C*P.x^d*P.fund) P.σ (Orchard I P.P.P h v P.Y x.1 x.2) (Orchard I P.P.Q h v P.Z x.1 x.2)
   obtain ⟨d,H⟩:= gazette _ S R (fun i hi=> Air.steeps (e:=e) (G:=G) ((Finset.mem_filter.mp hi).2) h v) (fun i _ I d e a b g p q h P=> (h P).step (logStep g p q P.P.rich P.large) P.P.θ)
   refine ⟨d,fun i=>?_⟩; obtain ⟨C,h,p⟩:= H i; refine ⟨C,h,fun P x y t v=>p (x,y) ?_ P⟩; apply Finset.mem_filter.mpr; exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show _ from by unfold lowerGrade at t; simp only; omega),Finset.mem_range.mpr (show y<r+1 from by omega)⟩,t⟩

lemma orchardTop (F:Frame G h) (H:Hol G)(p:h<D)(e k u r:ℕ)(hg:h+(h+1)≤u)(hp:(h+1)*r≤u)(hV:h*h≤u): ∃ d:ℕ,∀ I:Cloister G h,∃ C:ℝ,0≤ C∧∀ (P: SumT (inkPin I) e r D u)(_:Courant I P.P.P)(X:ℝ), P.η=1→ Stakes P.Y→ Standby (P.Y e r) → (∀ i< e,∀ j,Fruit 0 1 u (P.Y i j) P.fund) → (∀ i:Alma F,valence F i=r→ glean F P.Y e i=0) → Fruit 0 1 u (P.Y e r) X →
   let B:=I.lamp; let Z:=Orchard (inkPin I) P.P.P h k P.Y; let W:= C*P.x^d*P.fund
   Fruit 0 1 u (Z e r) ((permeability H F p u r B)/(inkPin I).patch.L.val * X + W)∧∀ i:Alma F,valence F i=r → ‖echoS F (Z e r) i‖≤W:=by
   obtain ⟨d,H'⟩:= Air.paintH (e:=e) (G:=G) (r:=r) (D:=D) (u:=u) k; let V:= (echo_credit F hV r D).choose; have hv:0≤V:= (echo_credit F hV r D).choose_spec.1
   refine ⟨d,fun I=>?_⟩; obtain ⟨A,hA,f⟩:= H' (inkPin I); obtain ⟨T,hT,H⟩:= Hall_tower F H p u r hg hp hV I e
   let W:=(inkPin I).patch; let c:=gradeH W h k; have hc:0≤c:= grade_nn ..; let R:=c*A; have hR:0≤R:=by unfold R; positivity
   refine ⟨T+(R+V*R),by positivity,?_⟩; intro P S X hQ q p' g u0 hC B Z L; have he:1≤ P.x:=P.P.rich; have hy:= P.large
   obtain ⟨ht,hv'⟩:= H P.P.P S P.Y P.fund X P.large q g u0 ((P.P.Υ.mono (B.outlet.trans B.path.holds.le)).oneP) p' hC
   let y:= P.x^d; let A:= c • (carnival (inkPin I) P.P.P k P.Y e r+veering (inkPin I) P.P.P k P.Y e r); let E:=hall W h P.P.P.Q (P.Y e r)
   have ha:Z e r= E+A:=by unfold Z Orchard; rw [Pi.smul_apply,Pi.smul_apply,helmet_bows,smul_add]; unfold hall E; rw [hall,smul_smul,gradeBB]
   have hx:= (f P).wax; change Fruit 0 P.η u _ _ at hx; rw [hQ] at hx; have hk: Fruit 0 1 u A (R*y*P.fund):= by unfold A; have hu:= hx.μ c; rw [abs_of_nonneg hc] at hu; exact hu.more (le_of_eq (by unfold R y SumT.x xpos Trump; ring))
   have hh:1≤ y:= one_le_pow₀ he; have hT':T*P.fund≤ T*y*P.fund:= mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hT hh) hy
   rw [ha]; refine ⟨(ht.plus hk zero_le_one).more ?_,fun i g=>?_⟩
   · rw [add_assoc]; apply add_le_add_right; refine (add_le_add_left hT' (R*y*P.fund)).trans ?_; change _ ≤ (T+(R+V*R))*y*P.fund; rw [← add_mul,← add_mul]; gcongr; exact le_add_of_nonneg_right (by positivity)
   rw [echoLP_add F i ht hk hV]; apply (norm_add_le ..).trans ((add_le_add (hv'.tell i (weigh_cap ..) g) ((echo_credit F hV r D).choose_spec.2 i A _ hk)).trans ?_)
   apply le_trans (add_le_add_left hT' _)
   change _≤ (T+(R+V*R))*y*P.fund; rw [show T*y*P.fund+ V*(R*y*P.fund)=(T+V*R)*y*P.fund from by ring]; gcongr; exact le_add_of_nonneg_left hR
end YM.WilsonCoeffUV.Shard
