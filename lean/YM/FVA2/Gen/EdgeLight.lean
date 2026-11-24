import YM.FVA2.Gen.RealJ
import YM.Work.G03
/-! # Sampling smooth connections along manuscript positive real edges -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Maxwell Labels Precision Lattice RG Wilson Source
variable {G:Gauge}{A: Sky G}{J J':Jet G}{f:Mist G}{u:E4→G.El}{x:E4}{i j:Axis}
local notation "P"=> E4
local notation "C"=> G.Color
local notation "δ"=> par
local notation "U"=> G.mat
local notation "Γ"=> G.colorMat
open Work.G03
abbrev spot (e:Edge Cover) (t:ℝ):= castPos e.1+t • basis e.2
/-- ALL positive link flows. Input continuous only per A. Need Fluid to produce. Treat dependence separately. -/
def slides (A:Sky G) (e:Edge Cover) (y:ℝ×ℝ):= y.1 • A e.2 ( y.1 • spot e y.2 )
abbrev Breeze (G:Gauge):= ℝ→Edge Cover→ℝ→G.El
def Air (p:Breeze G) (A:Sky G): Prop:=∀ l:Edge Cover, Meets ( slides A l ) (fun y:ℝ=> p y l)
lemma barC (hf:Fluid A)(l:Edge Cover) : ContDiff ℝ ∞ (slides A l):= ContDiff.smul (f:=Prod.fst) contDiff_fst ( show ContDiff ℝ ∞ (fun t:ℝ×ℝ=> A l.2 (t.1 • spot l t.2)) from (hf l.2).comp (f:=fun t:ℝ×ℝ=> t.1 • spot l t.2) (contDiff_fst.smul ( contDiff_const.add (contDiff_snd.smul contDiff_const) )) )
lemma skyway_air (h: Fluid A): ∃ p:Breeze G,Air p A:=by choose Q h using fun l:Edge Cover=> meets_real ( barC h l ); exact ⟨fun y l=> Q l y,h⟩
abbrev bookend (p:Breeze G)(t:ℝ) : CoverConfig G:= fun e=> p t e 1
abbrev groundC (a:ℝ) (u:P→G.El) (x: Cover):= u ( a • castPos x )
variable {p q:Breeze G}
private lemma invoke (h:Lived u)(t s:ℝ) (e:Edge Cover): HasDerivAt (fun v:ℝ=> G.mat (u (s • spot e v)))
 ( s • δ (basis e.2) ( U∘u ) (s • spot e t) ) t:= by
    let b:P:= s • basis e.2; let x:= castPos e.1; have hh(v:ℝ): s • spot e v=s • x+ v • b:= by unfold spot b x; rw [ smul_add,smul_comm s v ]
    simp_rw [hh]; obtain he:= par_line (h.differentiable (by simp)) b (s • x) t; have hp : ∀ z, δ b (U ∘ u) z=s • δ (basis e.2) (U ∘ u) z:= fun z=> map_smul ..; rw [ hp ] at he; exact he
-- easier gauge-cov using product p' * u(path) HOT, differential matches original.Leave initial handled. Compute without inverse derivative.
lemma Edge_gau (P₀:Air p A)(P₁:Air q (skyturn u A))(h:Lived u)(t:ℝ): bookend q t=Lattice.gauge (groundC t u) (bookend p t):= by
 funext ⟨x,i⟩; let e:Edge Cover:=(x,i); let a:=p t e; let b:=q t e; let X:=slides A e; let Q:ℝ→G.El:=fun s:ℝ=>u ( t • spot e s ); let F(s:ℝ):= (Q 0)⁻¹ * ( b s * Q s ); let R:= F; have hf:= P₀ e t; have hq:= P₁ e t; have Hs (s:ℝ): HasDerivAt (fun v:ℝ=> U (b v * Q v)) (U (b s*Q s) * Γ (X (t,s))) s:= by
    simp_rw [G.mat_mul]; apply (( hq.2 s ).mul ( invoke h s t e )).congr_deriv; -- use skyline multiplied
    let y:=t • spot e s; let c:= U (Q s); let D:= U (b s)
    let f:= hat G (skyturn u A i) y; let k:= hat G (A i) y; let d:=δ (basis i) (U ∘ u) y; change D * Γ (t • skyturn u A i y) * c + D * (t • d) = D*c* Γ (t • A i y); simp only [ map_smul ]; change D * (t • f) * c + D * ( t • d ) = D*c*(t • k); rw [ mul_smul_comm,mul_smul_comm,mul_smul_comm, smul_mul_assoc, mul_assoc,mul_assoc D c, ← smul_add, ← mul_add, show f*c=c*k-d from skyline h, sub_add_cancel ]
 have HH: SolvesLink F (fun s:ℝ=> X (t,s)):=by
    refine ⟨?_,fun v=>?_ ⟩; · unfold F b; simp [ P₁ e t|>.1 ]
    unfold F; change HasDerivAt (fun x=> (star (U (Q 0)))*U ( b x * Q x )) ((star (U (Q 0))) * U (b v * Q v) * _) v; rw [mul_assoc]; exact ( Hs v ).const_mul _
 let y':= x+step i; have ht0:Q 1=groundC t u (x+step i) := by unfold Q groundC spot; dsimp only [e]; rw [ one_smul,castPos_step ]
 have h₀: Q 0=groundC t u x:=by unfold Q groundC spot; simp [e]
 change b 1= groundC t u x*a 1*(groundC t u (x+step i))⁻¹; rw [← h₀,← ht0]; apply eq_mul_inv_iff_mul_eq.mpr; exact Eq.trans ( show b 1 * Q 1 = Q 0*F 1 from (by simp [F]) ) ( congrArg (fun a=>Q 0*a) ( congr_fun (HH.unique hf) 1 )) -- fix orientation
end YM.FVA2.Gen
