import YM.WilsonCoeffUV.Vacuum.Step.Strict
/-!
# Reclosure on complete axis read. Prices and continuity on strict slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{i j ℓ n k e r:ℕ}{s A B C δ : ℝ}

lemma scoopedY {P Q:(i:Gear G) → Rally k r i→ Ten ℝ (Cloth (Helms i)) j}{s:Gear G→ℝ} (h:Satin (largus k r) (smallus k r) s P Q): Satin (largus k r) (smallus k r) s (fun i t=> scoop (P i t)) (fun i t=>scoop (Q i t)) := Satin.spare h
lemma note_partial (e r:ℕ): Satin (largus e r (G:=G)) (smallus e r) Gear.σ (fun _ x=>x.P.flashback r e) (fun _ x=>x.Q.flashback r e):= by
   have hs : ∀ i:Gear G,0≤ i.σ:= fun i=>i.price.le
   unfold Stand.flashback; apply Satin.add (scoopedY (P:=fun i x=>intake i x.P e r) (intake_frames (G:=G) (w:=Gear.σ) e e r r hs Gear.holds)) _ (fun I=>permits I e r)
   apply Satin.sum (fun I=>permits I e r); intro i _; exact scoopedY (P:=fun _ x=>x.P.rays (i+1) e r) (Satin.flywheel (G:=G) (i+1) e r e r (by omega) _ Gear.holds hs)
lemma kernel_pair {X Y: ropes Cover (Hooks G) (Hooks G)}(h:Ballast s A δ X Y)(i j): PairA s A δ (flatPal X i j) (flatPal Y i j):=by
    have e: PairA s A δ (orbQ X) (orbQ Y):= ⟨drag_orb h.oneP, drag_orb h.otherP,by rw [show orbQ X-orbQ Y=orbQ (X-Y) from funext (fun i=>by simp only [Pi.sub_apply,orbQ,Matrix.sub_apply]; ring)]; exact drag_orb h.between⟩
    let hQ (j): PairA s A δ (0:Ten ℝ (YForest G) j) 0:= ⟨Amber.zero.le h.nn, Amber.zero.le h.nn,by rw [sub_zero]; exact Amber.zero.le h.between.1⟩
    unfold flatPal; split
    · by_cases H:2=j
      · subst j; simp only [shine_lit]; exact e
      simp only [shine_dark H]; exact hQ _
    exact hQ _
lemma Satin.delta_full (h:lowerGrade e i k r): Satin (largus k r (G:=G)) (smallus k r) Gear.σ (fun _ x=>x.P.driftU e i) (fun _ x=>x.Q.driftU e i):=by
   have hv n: Satin (largus k r (G:=G)) (smallus k r) Gear.σ (fun I x=>x.P.rays n e i) (fun I x=>x.Q.rays n e i) := flywheel n e i k r (by unfold lowerGrade at h; omega) _ Gear.holds (fun I=>I.price.le)
   have H: Satin (largus k r (G:=G)) (smallus k r) Gear.σ (fun I x=>snow I.patch I.kernel I.angle x.P.R x.P.Q x.P.page e i) (fun I x=> snow I.patch I.kernel I.angle x.Q.R x.Q.Q x.Q.page e i) :=by
       simp_rw [snow,sluice, Finset.sum_apply]; exact scoopedY (P:=fun (I:Gear G) x=>∑ j∈Finset.range (3+3*e), x.P.rays j e i) (Satin.sum (fun I=>permits I k r) (fun j _=>hv j))
   have he : Satin (largus k r (G:=G)) (smallus k r) Gear.σ (fun I x=> flatPal x.P.Z e i) (fun I x=>flatPal x.Q.Z e i):= ⟨0,fun I=> ⟨I.D,zero_le_one.trans I.bill_nn,fun j=> by rw [pow_zero,mul_one]; exact kernel_pair (j.Ω.mono I.holds.le) e i⟩⟩
   have H' (I:Gear G): ∃ A, Amber terrain I.σ A (uband (U:=YForest G) (perζ I.kernel I.angle) e i) := by
       unfold uband; by_cases h':0=i
       · subst i; simp only [shine_lit]; refine ⟨‖coeff e (perζ I.kernel I.angle)‖,norm_nonneg _,fun x=>?_⟩; simp [soar,league]
       rw [shine_dark h']; exact ⟨_,Amber.zero⟩
   exact (he.sub H (fun I=>permits I k r)).add (Satin.fixed (P:=fun I=>uband (U:=YForest G) (perζ I.kernel I.angle) e i) (fun I=>permits I k r) H') (fun I=>permits I k r)

lemma note_kin {P Q: Ten ℝ (YForest G) 2}(h:PairA s A δ P Q)(e:0<s): twain (A*(ceilPoly 2 (s/2)*sheetPay (s/2))) δ (readSun P) (readSun Q):= by
   refine ⟨sun_cost h.pose e,sun_cost h.vale e,?_⟩; rw [← sun_sub h.pose h.vale e e]; exact (sun_cost h.visit e).trans_eq (by ring)

-- apply ratio operations to arbitrary Slate currencies
section
variable {I:Type*}{J:I→Type*}{x θ: (i:I)→ J i→ℝ}
private lemma ahead {p q:(i:I)→ J i→ℕ→ℝ}{S:Finset ℕ}(e:∀ i,Brite (x i) (θ i))(h:∀ j∈S,Slate x θ (fun i y=>p i y j) (fun i y=>q i y j)): ∃ d:ℕ,∀ i,∃ C:ℝ,1≤C ∧∀ j∈S,∀ y,twain (C*x i y^d) (θ i y) (p i y j) (q i y j):=by
   induction S using Finset.induction_on with
   | empty=> exact ⟨0,fun _=>⟨1,le_rfl, by simp⟩⟩
   | @insert j S he ih=>
     obtain ⟨d,H⟩:= h j (Finset.mem_insert_self ..); obtain ⟨t,H'⟩:= ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)); refine ⟨d+t,fun i=>?_⟩
     obtain ⟨a,hp,F⟩:= H i; obtain ⟨b,hB,g⟩:= H' i; refine ⟨max a b, le_max_of_le_right hB,?_⟩
     intro k hk y; have ht:= (e i).large y; rcases Finset.mem_insert.mp hk with hb|hb
     · subst k; apply (F y).lift _ ((e i).dist _); exact mul_le_mul (le_max_left ..) (pow_le_pow_right₀ ht (by omega)) (pow_nonneg (zero_le_one.trans ht) _) (le_max_of_le_left hp)
     apply (g k hb y).lift _ ((e i).dist _); exact mul_le_mul (le_max_right ..) (pow_le_pow_right₀ ht (by omega)) (pow_nonneg (zero_le_one.trans ht) _) (le_max_of_le_left hp)
lemma rapture {p q:(i:I)→ J i→PowerSeries ℝ}(e:∀ i,Brite (x i) (θ i))(he:∀ i j,constantCoeff (p i j)=1)(hv:∀ i j,constantCoeff (q i j)=1)(r a b)(hx:∀ j≤r,Slate x θ (fun i y=>coeff j (p i y)) (fun i y=>coeff j (q i y))):
   Slate x θ (fun i j=> coeff r ((back (p i j))^a*((back (p i j))⁻¹)^b)) (fun i j=> coeff r (back (q i j)^a*((back (q i j))⁻¹)^b)) := by
    obtain ⟨d,H'⟩:= ahead (p:=fun i j k=>coeff k (p i j)) (q:=fun i j k=>coeff k (q i j)) (S:=Finset.range (r+1)) e (fun j hj=> hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    obtain ⟨n,C,hC,H⟩:=scalar_receipt r a b; refine ⟨d*n,fun i=>?_⟩; obtain ⟨A,hp,h⟩:= H' i
    have ht:= zero_le_one.trans hp; refine ⟨C*A^n, by positivity,fun j=>?_⟩
    let P: ScalarGate r:= ⟨A*x i j^d,θ i j,one_le_mul_of_one_le_of_one_le hp (one_le_pow₀ ((e i).large j)),(e i).dist j,p i j,q i j,he i j,hv i j,fun k hk=>h k (Finset.mem_range.mpr (by omega)) j⟩
    rw [pow_mul,mul_assoc,←mul_pow]; exact H P
end
lemma titles {i e:ℕ}(h:i< e)(r a b): Slate (largus e r (G:=G)) (smallus e r)
    (fun _ x=> coeff i (x.P.moving^a*(x.P.moving⁻¹)^b)) (fun _ x=>coeff i (x.Q.moving^a*(x.Q.moving⁻¹)^b)):=by
   let A: (I:Gear G)→ Rally e r I→PowerSeries ℝ:= fun _ x=> Kstar x.P.driftU
   let B: (I:Gear G)→ Rally e r I→PowerSeries ℝ:= fun _ x=> Kstar x.Q.driftU
   have he j (hj:j≤ i): Slate (largus e r) (smallus e r) (fun y t=>coeff j (A y t)) (fun y t=>coeff j (B y t)):=by
      simp only [A,B,stellar_read]; exact Satin.haul (P:=fun (I:Gear G) (x:Rally e r I)=>x.P.driftU j 2) (Q:=fun (I:Gear G) (x:Rally e r I)=>x.Q.driftU j 2) (Satin.delta_full (show lowerGrade j 2 e r from Or.inl (by omega))) Gear.price
   have hp:= rapture (p:=A) (q:=B) (fun I=>permits I e r) (fun _ y=> y.P.sunshine) (fun _ y=> y.Q.sunshine) i a b he
   exact hp
end YM.WilsonCoeffUV.Bank
