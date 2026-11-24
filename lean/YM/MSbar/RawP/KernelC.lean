import YM.MSbar.RawP.Roil
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side} {a b C Z B w K r:ℝ}{p k:ℕ}
open Metric Pressure AnalyticBridge.SectorAffine.Offset
local notation "W₀"=>Positions (Primary n G)
variable (P:PathData G)(t:Clip)(S:Signed)(A:ℕ→Atom G k) {x:Positions (Primary n G)}
lemma uniqueF (S:Signed)(n:Side): Injective (affine S (0:Site n)):=fun _ _ h=> S.act_injective (add_right_cancel h)
variable (h:P.Bounds t (a+2*(3*b)*p) C r) (hP: PaintSupply G p K) (hB:Wind G a Z p)(hA:SumBudget (fun i=> (A i).budget (a+2*(3*b)*p)) C)(hx:‖x‖<1)(hb:0<b)
local notation "Λ"=> sparkP S
noncomputable def pulp (Z b C:ℝ)(p k:ℕ) := (2^p*Z)^k*C*Real.exp ((3*b)*p)*countCost b
include hA hx hB hb
lemma cyst : Roil (fun x:W₀=> uncut A (sparkP S x)) p b x (pulp Z b C p k) :=by
    let H(b:Site n)(x:W₀):=∑' i,(A i).unmasked (sparkP S x) b; have he(b':Site n):= tents S b' hB hx hA (show 0≤3*b by positivity); have hZ:=hB.1; have ht:0 ≤ C:= (hA.2.2 |> le_trans (tsum_nonneg hA.1)); unfold pulp
    apply Roil.mono (f:=fun x:W₀=>∑ b:Site n,H b x) (Roil.stock H (affine S 0) (fun b=>he b|>.1.1) (fun b=>he b|>.2) (by positivity) hb (Multiplicity.injective (uniqueF S n))); simp
omit hA
variable (δ:ℝ)(hV:∀ v:G.Color, ‖v‖ ≤ Z*C→ Allows p coinP v δ)
include h hV hP
noncomputable def kernelCost (G:Gauge)(t:Clip)(C K Z b δ:ℝ)(p:ℕ):= ((|t.direct| *priceA G p K)*Real.exp ((3*b)*(p*5:ℕ))+bucket p δ (Z*C) (Real.exp ((3*b)*p))) * (Fintype.card PlaqAxes * countCost b)
local notation "Q"=>kernelCost G t C K Z b δ p
lemma grain : Roil (fun x:W₀ => quadratic t P (sparkP S x)) p b x Q :=by
    let f(b':Face (Per n))(v:W₀):= t.direct*penG G b' S v+‖P.ell (Λ v) b'‖^2/2; let w (q:Face (Per n)):= affine S (0:Site n) q.1; have hg(z:Pressure.Bond n) : ContDiffAt ℝ ω (fun y:W₀=> G.mat (Λ y z)) x := (votes S z x hP hx.le).analytic; have hi(q :Face (Per n)): ContDiffAt ℝ p (f q) x:=by
         let g(y:W₀):=faceValue (Λ y) q; have hh:Allows p (fun y=> G.mat (g y)) x (travelCost G p 4 (outerCost G p K)):= travel_jets (U:=fun v:W₀=>sparkP S v) (fun i=> votes S i _ hP hx.le) (w:=square q.2.val.1 q.2.val.2) q.1 (le_refl 4)
         exact (ContDiffAt.add ((hh.price (f:=g)).analytic.const_smul t.direct) (((contDiff_norm_sq ℝ).contDiffAt.comp x (Work.F02.ell_contDiffAt h q hg)).div_const 2)).of_le le_top
    let g':= (|t.direct| *priceA G p K)*Real.exp ((3*b)*(p*5:ℕ))+bucket p δ (Z*C) (Real.exp ((3*b)*p)); have hh(q:Face (Per n)):Beacon (Measuring.chart n G) (3*b) p (f q) (w q) x g':=earning S q hB hx h (by positivity) hP δ hV; let I:=Fintype.card PlaqAxes; have hz:0≤ g':=by
        let b':Face (Per n):=(0,Classical.arbitrary _); have hx:= hh b' 0 (by omega) (fun i:Fin 0=>i.elim0); rw [show spanSites _ _ _=0 from (by unfold spanSites;simp),Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hx; exact (norm_nonneg _).trans hx
    apply Roil.stock f w hi hh hz hb; intro y; have hf:= Finset.card_le_card_of_injOn (s:=Finset.univ.filter fun i=>w i=y) (t:=(univ:Finset PlaqAxes)) Prod.snd (fun i hi=> mem_univ _) (fun i hi j hj hij=> Prod.ext (uniqueF S n ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)) hij); exact hf.trans_eq card_univ
local notation "J"=> Q+pulp Z b C p 3+pulp Z b C p 4
lemma hullC : Roil (collectT n P t) p b x (Q+pulp Z b C p 3+pulp Z b C p 4) :=by
    let f(s:Signed)(x:W₀):= quadratic t P (sparkP s x)+uncut P.cubic (sparkP s x)+ uncut P.quartic (sparkP s x); have he(s): Roil (f s) p b x (J):=Roil.plus (Roil.plus (grain P t s h hP hB hx hb δ hV) (cyst s P.cubic hB h.three hx hb)) (cyst s P.quartic hB h.four hx hb); let K:=(Fintype.card Signed:ℝ)
    refine Roil.mono (Roil.scale (Roil.unite f _ univ (fun i _=> he i)) (K⁻¹)) ?_; rw [abs_of_nonneg (by unfold K; positivity : 0≤K⁻¹),sum_const,nsmul_eq_mul,card_univ]; rw [show (Fintype.card Signed:ℝ)=K from rfl, inv_mul_cancel_left₀ (by unfold K; positivity)]
omit hP hV
lemma loopC : Roil (liveLoop n P) p b x (pulp Z b r p 2):=by
    let f(s:Signed)(x:W₀):= uncut P.loop (sparkP s x); have he(s): Roil (f s) p b x (pulp Z b r p 2):= cyst s P.loop hB h.two hx hb; let K:=(Fintype.card Signed:ℝ); refine Roil.mono (Roil.scale (Roil.unite f _ univ (fun i _=> he i)) (K⁻¹)) ?_; rw [abs_of_nonneg (by unfold K; positivity : 0≤K⁻¹),sum_const,nsmul_eq_mul,card_univ]; rw [show (Fintype.card Signed:ℝ)=K from rfl, inv_mul_cancel_left₀ (by unfold K; positivity)]
end YM.MSbar.RawP
