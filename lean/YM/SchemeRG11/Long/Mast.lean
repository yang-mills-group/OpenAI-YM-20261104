import YM.SchemeRG11.Long.Travel
/-! Dyadic payments for ANY degree legs. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn
open scoped Classical
variable {G: Gauge} {m n:ℕ} {T: Align.Itinerary}
variable {a b:Touch G}
local notation "D₁" => Atoll.land G
lemma convoy (s:Fliers):Plain T (-(s.card:ℤ)-2) (view (fleet s Cellular.coverLine)):=by
 induction s using Quotient.inductionOn with | _ l=>
 obtain ⟨C,hC,H⟩:=Catch.payment l; have ht(p:ℝ): -(l.length:ℤ)-2=-((l.length+2:ℕ):ℤ):=by push_cast; ring
 refine ⟨⟨C,hC,Eventually.of_forall (fun k z _=> ?_)⟩,fun z hz _ p hp=> ?_⟩
 · change |fleet (l: Fliers) _ z| ≤ _; rw [ruralDerivative]; change _≤ C * _ * d z ^ (-(l.length:ℤ)-2); rw [zpow_zero,mul_one,ht 1,zpow_neg,zpow_natCast]; exact (le_div_iff₀ (pow_pos (d_pos z) _)).mpr (H z)
 refine ⟨_, (Catch.offLine T p l hz hp).congr ?_⟩; intro i; change _= T.gap i ^ (-(l.length:ℤ)-2)*fleet (l:Fliers) _ _; rw [ruralDerivative,ht 1,zpow_neg,zpow_natCast,inv_pow]
lemma sold (s t:Fliers)(a b:Shaft G): Plain T (-((s.card:ℤ)+1)-((t.card:ℤ)+1)) (view fun z=>(D₁).bed (flex z (vane0 a s)) (vane0 b t)):=by
 let f(z:Cover):=(D₁).bed (flex z (idi a)) (idi b); let C:= (-1:ℝ)^t.card
 have hh(z): (D₁).bed (flex z (vane0 a s)) (vane0 b t) = C*fleet (s+t) f (z+streak t):=dualDrive ..
 simp_rw [hh]
 have hp (z:Cover): f z=(if a.2=b.2∧a.1.2=b.1.2 then (hop (a.1.1-b.1.1) Cellular.coverLine) z else 0):=by
   unfold f; rw [flex_one,Dose.bed, grain,Haze.Dose.single_wind]; unfold Atoll.land; simp only [rise]; split
   · congr 1; abel
   rfl
 by_cases h:a.2=b.2∧a.1.2=b.1.2
 · have ht : f=hop (a.1.1-b.1.1) Cellular.coverLine:=funext fun z=>(hp z).trans (if_pos h)
   rw [show -((s.card:ℤ)+1)-((t.card:ℤ)+1) = -((s+t).card:ℤ)-2 from by simp; omega]
   simp_rw [ht,jump]
   convert ((convoy (T:=T) (s+t)).moved (streak t+a.1.1-b.1.1)).scale C using 1; funext i z
   change C*fleet (s+t) Cellular.coverLine _=C*fleet (s+t) Cellular.coverLine _; rw [show z+streak t+(a.1.1-b.1.1)=streak t+a.1.1-b.1.1+z by abel]
 have he:f=0:=funext fun z=> (hp z).trans (if_neg h)
 rw [he,map_zero, show view (fun z=>C*(0:Plane ℝ) (z+streak t))=0 from by simp;rfl]; exact Plain.zero
lemma vats (hx:a∈Stepper G n)(hv:b∈Stepper G m):Plain T (-((n:ℤ)+1)-((m:ℤ)+1)) (view fun z=>(D₁).bed (flex z a) b):=by
 let u : ℤ:= -((n:ℤ)+1)-((m:ℤ)+1)
 induction hx using Submodule.span_induction with
 | mem f h=>
   obtain ⟨i,s,h,rfl⟩:=h
   induction hv using Submodule.span_induction with
   | mem g H=>
     obtain ⟨j,t,T',rfl⟩:=H; subst m; subst n; apply sold
   | zero=>simp only [Dose.bed,map_zero]; exact Plain.zero
   | add c d _ _ hc hd=>simp only [Dose.bed,map_add]; exact hc.add hd
   | smul r v _ h=> simp only [Dose.bed,map_smul]; exact h.scale _
 | zero=> simp only [map_zero, show ∀ w:Touch G,(D₁).bed 0 w=0 from fun w=> (double_comm (0:Touch G) w).trans (map_zero _)]; exact Plain.zero
 | add c d _ _ hc hd=>simp only [map_add,doub]; exact hc.add hd
 | smul c r _ h=>simp only [map_smul,paid_s]; exact h.scale _
lemma stamp (x:Touch G)(hx:x∈Stepper G n)(p:Sky G m): Plain T ((inkAge p:ℤ)-(n+1:ℤ)) (view fun z=>sense (cant (plum p)) (flex z x)):=by
 induction hx using Submodule.span_induction with
 | mem a h=>
   obtain ⟨i,s,H,rfl⟩:=h; subst n
   let f:= plume p; let C: G.Color→ₗ[ℝ]ℝ:=(EuclideanSpace.proj i.2).toLinearMap
   let u:ℤ:= inkAge p
   have hf: f∈team G.Color (inkAge p):= clouded _
   have ht:C ∘ f i.1.2∈ cap ℝ ((u-1+1).toNat) :=(show (u-1+1).toNat=inkAge p from by unfold u; omega) ▸ team_wing (team_linear C f _ hf) _
   simp_rw [dip,add_comm _ i.1.1]; rw [show (inkAge p:ℤ)-((s.card:ℤ)+1)= (u-1)-(s.card:ℤ) from by unfold u; ring]; exact (flight_cost _ _ ht s).moved i.1.1
 | zero=> simp only [map_zero]; exact Plain.zero
 | add c d _ _ hc hd=> simp only [map_add]; exact hc.add hd
 | smul r c _ h=>simp only [map_smul]; exact h.scale _
lemma sail {A:Bevy G.Color}(h:A∈team G.Color m)(hh:m≤ n)(p: Touch G)(hp:p∈Stepper G n) (z:Cover): sense (cant (linkup A)) (flex z p)=0:=by
 induction hp using Submodule.span_induction with
 | mem f g=> obtain ⟨i,s,H,rfl⟩:=g; rw [dip,across,member.mp (cap_height hh (team_wing h _)) s H]; rfl
 | zero=>simp
 | add a b _ _ ha hb=>rw [map_add,map_add,ha,hb, add_zero]
 | smul r p _ h=>rw [map_smul,map_smul,h,smul_zero]
end YM.SchemeRG11.Long
