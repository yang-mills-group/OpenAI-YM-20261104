import YM.AllOrder.Response.Booth
/-!
# Graded series expectation on moving paths, with both slots
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
open GaussianScore
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y][BorelSpace Y]
local notation "Ω"=> X×Y
variable (Γ:Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure] {u v:X×Y→ℝ}
def bound (Γ:Law Y)(μ:Measure Y)(u:Ω→ℝ)(x:X):= Γ.average μ (fun z=>u (x,z))
omit [MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in
lemma localP (h:Plausible u) (x:X): Plausible (fun z:Y=>u (x,z)):= by
   have he:= nearStep (B:=LinearMap.inr ℝ X Y) (x,0) h; simpa using! he
lemma bound_add (h:Plausible u)(H:Plausible v): bound Γ μ (u+v)=bound Γ μ u+bound Γ μ v:= funext fun i=> average_add Γ μ (localP h i) (localP H i)
lemma bound_scale (u:X×Y→ℝ)(x:ℝ):bound Γ μ (x • u)=x • bound Γ μ u:= funext fun i=> average_scale Γ μ x _
-- tensor closable with λ preserves Ψ
inductive Pledge (X Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup X] [NormedSpace ℝ X] : ((X×Y)→ℝ)→Prop
   | core {a:X→ℝ}{b:Y→ℝ} (ha:Plausible a)(hb:Plausible b) : Pledge X Y (fun p=>a p.1*b p.2)
   | add {u v : X × Y→ℝ} : Pledge X Y u → Pledge X Y v → Pledge X Y (u+v)
omit [MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in
lemma Pledge.mul (h:Pledge X Y u)(H:Pledge X Y v):Pledge X Y (u*v):= by
 induction H generalizing u with
 | @core a b h₁ h₂=>
   induction h with
   | @core U W h₃ h₄=>
       convert Pledge.core (h₃.mul h₁) (h₄.mul h₂) using 1; ext1 x; simp only [Pi.mul_apply]; ring
   | add _ _ i j=> rw [add_mul];exact i.add j
 | add hg hh i j=> rw [mul_add]; exact (i h).add (j h)
omit [MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in
lemma Pledge.p (h:Pledge X Y u):Plausible u:= by
 induction h with
 | core h h'=> exact (h.app (LinearMap.fst ℝ X Y)).mul (h'.app (LinearMap.snd ℝ X Y))
 | add _ _ i j=> exact i.add j
omit [MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in
lemma pension (h:Plausible u):Pledge X Y u:= by
 induction h with
 | atom c=> exact (show (fun (_:Ω)=> c*1)=(fun _=>c) by simp) ▸ (Pledge.core (Plausible.atom c) (Plausible.atom 1))
 | times g h hb ih=>
    let V := h.comp (LinearMap.inl ℝ X Y); let W:=h.comp (LinearMap.inr ℝ X Y)
    apply ih.mul; show Pledge _ _ _
    convert Pledge.add (Pledge.core (Plausible.line V) (Plausible.atom (1:ℝ))) (Pledge.core (Plausible.atom (1:ℝ)) (Plausible.line W)) using 1; ext1 ⟨x,y⟩; change h _= h (x,0)*1+1*h (0,y); simp [← map_add]
 | add _ _ i j=> exact i.add j
section cost
lemma core_bound (a:X→ℝ)(b:Y→ℝ) : bound Γ μ (fun p=>a p.1*b p.2)= (Γ.average μ b) • a:=by ext1 x; exact (average_scale Γ μ (a x) b).trans (mul_comm ..)
lemma smooth_bind (h:Plausible u): Plausible (bound Γ μ u):= by induction (pension h) with
  | core ha _=> rw [core_bound]; exact ha.scale _
  | add h₁ h₂ i j=>rw [bound_add Γ μ h₁.p h₂.p]; exact (i h₁.p).add (j h₂.p)
variable {P:ℝ→X} (hp:ContDiffAt ℝ ω P 0)
include hp
lemma transport_p (h:Plausible u)(n:ℕ): Plausible (fun z:Y=> someJ (fun x:ℝ=> u (P x,z)) n) ∧
   Γ.average μ (fun z:Y=> someJ (fun x:ℝ=> u (P x,z)) n)=someJ ((bound Γ μ u) ∘ P) n:= by
   induction pension h with
   | @core a b ha hb=>
       have hx:ContDiffAt ℝ ω (a ∘ P) 0:=ha.smooth.contDiffAt.comp _ hp
       let M:= a ∘ P
       have he(x:ℝ)(y:ℝ→ℝ) (hy:ContDiffAt ℝ ω y 0) : someJ (y*(fun _=>x)) n=x*someJ y n := ((by rw [mul_comm]; exact (eo_Act n hy).smul x : Act n (y*(fun _=>x)) (x • someJ y))).writes _ le_rfl
       rw [show (fun z:Y=> someJ (fun x=> (fun p:(X×Y)=> a p.1 * b p.2) (P x,z)) n)= (someJ M n) • b from funext (fun z=> (he (b z) M hx).trans (mul_comm ..)), average_scale,core_bound]; refine ⟨hb.scale _, (mul_comm ..).trans (((eo_Act n hx).smul _).writes _ le_rfl).symm⟩
   | @add f g hf hg i j=>
       obtain ⟨hi,hx⟩:=i hf.p; obtain ⟨hh,hz⟩:=j hg.p
       have hF (z:Y):ContDiffAt ℝ ω (fun x=> (f) (P x,z)) 0:= hf.p.smooth.contDiffAt.comp (f:=fun x=>(P x,z)) (0:ℝ) (hp.prodMk contDiffAt_const); have hG (z:Y):ContDiffAt ℝ ω (fun x=> g (P x,z)) 0:=hg.p.smooth.contDiffAt.comp (f:=fun x=>(P x,z)) (0:ℝ) (hp.prodMk contDiffAt_const)
       rw [show (fun z:Y=> someJ (fun x=> (f+g) (P x,z)) n) = (fun z=> someJ (fun x:ℝ=>f (P x,z)) n)+(fun z=> someJ (fun x:ℝ=>g (P x,z)) n) from funext fun z=> congr_fun (some_add (hF z) (hG z)) n]; rw [average_add Γ μ hi hh, hx,hz,bound_add Γ μ hf.p hg.p]; exact ⟨hi.add hh,(congr_fun (some_add ((smooth_bind Γ μ hf.p).smooth.contDiffAt.comp (0:ℝ) hp) ((smooth_bind Γ μ hg.p).smooth.contDiffAt.comp (0:ℝ) hp)) n).symm⟩
-- Put onto output book, no disconnected loops breakout
variable {t:Book (X×Y)}(ht:∀ i,Plausible (t i))
def cloud (Γ:Law Y)(μ:Measure Y)(t:Book (X×Y))(k:ℕ): X→ℝ:= bound Γ μ (t k)
include ht
lemma transport (n:ℕ): Plausible (fun z:Y=> weigh (fun x=> (P x,z)) t n) ∧ Γ.average μ (fun z:Y=>weigh (fun x=>(P x,z)) t n)= weigh P (cloud Γ μ t) n:=by
   let F i z:= someJ (fun x=> t i (P x,z)) (n-i)
   have hf:(fun z:Y=> weigh (fun x=>(P x,z)) t n)=∑ i∈Finset.range (n+1), F i :=funext fun i=> (Finset.sum_apply i (range (n+1)) F).symm
   have hp i := transport_p Γ μ hp (ht i) (n-i); rw [hf]; refine ⟨Plausible.sum (fun i _=>(hp i).1),?_⟩;rw [average_sum Γ μ (k:=Finset.range (n+1)) (a:=F) (fun i _=> (hp i).1)]; exact Finset.sum_congr rfl fun i _=> (hp i).2
end cost
end YM.AllOrder.Response
