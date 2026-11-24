import YM.OPE.Compatible.Waft.Ban
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
namespace PriceZ
variable {W L: Type}
variable {K:Sponsor G}{T: Seasons K}{v:W→ℝ}{P:ChartRatio G}
variable (A:(i':W)→Alps K T i (v i'))(X:W→Side)(H:∀ i,Even (X i).val)(V:∀ i,Plot (H i))
local notation "Y" j=>Libra.Keys G (Stand.Free (V j))
variable {q μ:W→ℝ} {g: W→ℝ}(Vj:∀ i,Bor (H i) (A i) (g i))
lemma wages (p:(j:W)→ (Y j)→ ℝ)(h:WindZ X e k q p)(ht:0 ≤ q)(hp:4 ≤ i)(hs:G.Simple): Cash X (4+e+4*k) q (fun j=>(penon (Bor.L (Vj j) (V j))).average (Chart.tangent G (Stand.Free (V j))) (p j)) :=by
     obtain ⟨c₀,H,hS⟩:=worldCap K.K i hp; obtain ⟨u,hU,hQ⟩:= h.cap
     let D:=quotaB (Shade G) c₀ k; let ℓ:= Real.sqrt (Fintype.card G.ColorIndex); let a:= 1+3*ℓ
     have hℓ:0 ≤ ℓ:= Real.sqrt_nonneg _; have ha:0 ≤ a:=by unfold a; positivity
     have hD:0 ≤ D:=by unfold D quotaB; positivity
     refine ⟨D*(u*a^k), by positivity, fun i=>?_⟩ -- ∀i unneeded x
     let n:=X i; let V':= V i; let H':= (Vj i).L V'; let v:ℝ:= n.val; let t:= u*v^e*q i; have hx:= W_le n; have hy:1 ≤ v^4:=one_le_pow₀ hx; have hp':0 ≤ t:=by have hg:0 ≤ q i:=ht i; unfold t; positivity -- positivity v needs (n.val:ℝ) pos
     have he:= pondPay (H:=_) V' (Vj i) hp hs (p i) t hp' k (show zoneR _ V' (p i) t k from ⟨h.zon i,fun x=>(hQ i x).trans_eq (by unfold care t v n;ring)⟩) c₀ (hS _ _ _ _); apply he.trans; change v^4 *D*(t*(1+(1+2*v^4)*ℓ)^k) ≤ _; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ (show 1+(1+2*v^4)*ℓ≤ a*v^4 from ?_) k) hp') (by positivity :0 ≤ v^4*D)).trans_eq ?_
     · positivity
     · unfold a; nlinarith
     unfold t; rw [mul_pow, pow_add, pow_add,pow_mul]; unfold v n;ring
lemma costGauge {v:W→ℝ}{u w:ℕ}(h:Cash X u q v)(hp:q≥0)(hv:q ≤ μ)(hz:u ≤ w): Cash X w μ v:=by
     obtain ⟨c,hc,ht⟩:=h; refine ⟨c,hc,?_⟩; intro i; apply (ht _).trans; gcongr <;> first | exact W_le ..| exact hv _| exact hp _
abbrev Permit (X:W→Side)(u:ℕ)(q:W→ℝ)(v:W→Token):=∀ i: Phase,Cash X u q fun k=>(v k).seq i.val
variable {x y:W→Token} {p':ℕ}
lemma Permit.gauge (h:Permit X m q x)(hp:q≥0)(hv:q≤ μ)(he:m ≤ e): Permit X e μ x:=fun i=> costGauge X (h i) hp hv he
lemma gold_minus {x:W→ℝ}(h:Cash X m q x): Cash X m q (-x):=by obtain ⟨c,hc,H⟩:=h; exact ⟨c,hc,fun x=>by simpa only [Pi.neg_apply,norm_neg] using H x⟩
lemma Permit.add (h:Permit X m q x)(hp:Permit X m q y): Permit X m q (x+y):=by intro i; fin_cases i <;>first|exact gold_plus (h 0) (hp 0)|exact gold_plus (h 1) (hp 1)|exact gold_plus (h 2) (hp 2)
lemma Permit.mul (h:Permit X m q x)(hp:Permit X e μ y)(hv:0≤ q): Permit X (m+e) (q*μ) (x*y):=by intro i; fin_cases i; exact gold_times (h 0) hv (hp 0); exact gold_plus (gold_times (h 0) hv (hp 1)) (gold_times (h 1) hv (hp 0));exact gold_plus (gold_plus (gold_times (h 0) hv (hp 2)) (gold_times (h 1) hv (hp 1))) (gold_times (h 2) hv (hp 0))
lemma Permit.inv (h:Permit X m 1 x)(hp:∀ i,(x i).s=1) : Permit X (m+m) 1 x⁻¹:=by
     let P(i):=(x i).l
     let A(i):=(x i).h; have ht:Cash X (m+m) 1 P:= (Permit.gauge X h zero_le_one le_rfl (le_add_of_nonneg_right (Nat.zero_le m))) 1; have hQ:= (show Cash X (m+m) 1 (P*P) from by simpa only [one_mul] using! gold_times (h 1) (p:=1) zero_le_one (h 1)); intro i;fin_cases i
     · have hV(i:W):((x⁻¹) i).seq 0=(x i).seq 0:=by rw [Pi.inv_apply];change _⁻¹=(x i).s; simp_rw [hp,inv_one]
       convert! costGauge X (h 0) zero_le_one (le_refl _) (show m ≤ m+m by omega) using 2 with j; exact hV _
     · convert! gold_minus X ht using 2 with j; change (-(x j).l/(x j).s^2)= _; simp only [hp j];simp; rfl
     convert! gold_plus hQ (gold_minus X (costGauge X (show Cash X m 1 A from h 2) zero_le_one le_rfl (show m≤m+m by omega))) using 2 with j; change ((x j)⁻¹).h= _; -- name
     rw [JetS.sp_h,hp]; simp[pow_two,P,A,sub_eq_add_neg]
lemma weightsP (p:(i:W)→ScriptJ (Y i))(h:WindT X m k q p)(hta:q≥0)(hp:4 ≤ i)(hs:G.Simple):
    Permit X (4+m+4*k) q fun j=> draw (p j) (penon ((Vj j).L (V j))) (Chart.tangent G (Stand.Free (V j))):=by
         intro i; fin_cases i <;>first|exact wages _ X H V Vj _ (h 0) hta hp hs|exact wages _ X H V Vj _ (h 1) hta hp hs|exact wages _ X H V Vj _ (h 2) hta hp hs
lemma channelP {Z:(i:W)→ScriptJ (Y i)}{F:(i:W)→ScriptJ (Y i)}(h:WindT X m k q Z)(hx:q≥0)(hV:∀ i j,(F i j).s=1)(ht:WindT X r l 1 F)(hp:4 ≤ i)(hs:G.Simple):
    Permit X (4+(m+r)+4*(k+l)+(4+r+4*l+(4+r+4*l))) q (fun i=> fair (Chart.tangent G (Stand.Free (V i))) (penon ((Vj i).L (V i))) (F i) (Z i)):=by
         let μ(i:W):= Chart.tangent G (Stand.Free (V i)); let L(i):= penon ((Vj i).L (V i)); let A(i):= draw (F i) (L i) (μ i); let B(i):=draw (Z i*F i) (L i) (μ i)
         have hv: Permit X (4+r+4*l) 1 A:= weightsP _ X H V Vj _ ht zero_le_one hp hs; let p' := (fun i=> fair (μ i) (L i) (F i) (Z i)); rw [show (fun i=> fair _ _ _ _)=B*A⁻¹ from rfl]; simpa only [mul_one] using! (Permit.mul X (weightsP _ X H V Vj _ (h.prod ht hx) (show q*1 ≥0 from by rw [mul_one];exact hx) hp hs) (Permit.inv X hv fun i=> Shift.headD _ _ _ (hV i)) (show q * 1 ≥0 from by simpa using! hx))
end PriceZ
end YM.OPE.Quit
