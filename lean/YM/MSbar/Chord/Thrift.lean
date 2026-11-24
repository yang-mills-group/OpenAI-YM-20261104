import YM.MSbar.Chord.Driver
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{a D C Λ:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> (n.val:ℝ)
local notation "Θ"=>G.Color
variable (e:G.Color)(R:PathData G)(q:Clip)(hp:R.Bounds q a C Λ) (s: Signed) (p:ℕ) (hr:10*(p+4)<n.val)(b:Face (Per n)) (hE:‖e‖ ≤1)
local notation "J"=> tuner e
local notation "Q"=> url n p a
lemma spreadR (a:ℝ)(p:ℕ)(n:Side) : 0 ≤url n p a:=by unfold url size; positivity
-- product series from row inputs

noncomputable def stack (A : Θ): Θ→ₗ[ℝ]ℝ:= (innerSL ℝ (E:=G.Color) A).toLinearMap
noncomputable def stacker (G:Gauge): G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ where
    toFun:=stack
    map_add' u v:= LinearMap.ext (fun w=> by change ⟪u+v,w⟫_ℝ =⟪u,w⟫_ℝ+⟪v,w⟫_ℝ; rw [inner_add_left])
    map_smul' r u:= LinearMap.ext (fun w=> by change ⟪r•u,w⟫_ℝ= r*⟪u,w⟫_ℝ; rw [real_inner_smul_left])
lemma stack_read (G:Gauge)(x y:G.Color):stacker G x y= inner ℝ x y:=rfl
private lemma thin (δ : Θ→ₗ[ℝ]Θ→ₗ[ℝ]ℝ){u v :ℕ→Θ} (h:Summable u)(he: Summable v):
    ∑' z:ℕ ×ℕ,δ (u z.fst) (v z.snd) = δ (∑' i,u i) (∑' i,v i) ∧ Summable (fun z:ℕ×ℕ=> δ (u z.fst) (v z.snd)) :=by
    let L:= LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ δ)
    have hx: Summable fun i:ℕ×ℕ=> ‖u i.fst‖ *‖v i.snd‖:= summable_mul_of_summable_norm (f:=fun i=>‖u i‖) (g:=fun i=>‖v i‖) h.norm.norm he.norm.norm
    have hh:Summable (fun i:ℕ×ℕ=> δ (u i.fst) (v i.snd)):=Summable.of_norm_bounded (hx.mul_left ‖L‖) (fun i=> by refine (ContinuousLinearMap.le_opNorm (L (u i.fst)) (v i.snd)).trans ((mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)).trans_eq (mul_assoc ..)))
    have hv (x : Θ) : (∑' i, δ x (v i))=δ x (∑' i,v i):=((L x).map_tsum he).symm
    refine ⟨?_,hh⟩; rw [Summable.tsum_prod' hh (fun i=> ?_)]; simp_rw [hv]; exact ((δ.flip (∑' i,v i)).toContinuousLinearMap.map_tsum h).symm
    exact ((he.hasSum.mapL (L (u _))).summable) -- syntax
include hp hE hr
noncomputable def setting (b:PlaqAxes): Θ := ∑' i, (R.row b i).1 • mark (R.row b i).2.plaq e s
lemma wheelPrice (b:Face (Per n)): |gross (fun x y:Positions (Primary n G)=> inner ℝ (unionC s R b x) (unionC s R b y)) e -(-2*inner ℝ (setting e R s b.2) (setting e R s b.2))| ≤ C*C*url n p a:=by
    let f(i):=R.row b.2 i; let g(i)(x:X):=(f i).1 • curlX s (slotFace (f i).2 b.1) x
    let v(i):=(f i).1 • mark (f i).2.plaq e s; have he:=row_abs_summable R hp b.2; have ht(x:X): Summable (fun i=>g i x) := ellLine_summable R hp b (Bid.pulled ((tint G (Exterior.Body 1 n)) x) s)
    have hh : Summable v:=Summable.of_norm_bounded (he.mul_right ‖e‖) (fun i=>by unfold v; rw [norm_smul,Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_left (markN ..) (abs_nonneg _))
    let I:_:=stacker G; let X'(i:ℕ×ℕ)(x y:X):=inner ℝ (g i.1 x) (g i.2 y); have hF(x:X)(y:X) : (∑' i:ℕ×ℕ,X' i x y)= inner ℝ (unionC s R b x) (unionC s R b y) ∧ Summable (fun i=> X' i x y):=by change (∑' z:ℕ ×ℕ,I (g z.1 x) (g z.2 y)) = I (∑' i,g i x) (∑' i,g i y)∧_; exact thin I (ht x) (ht y)
    let K(i:ℕ×ℕ):= gross (X' i) e; obtain ⟨hA,hP⟩:= mosaic e X' (fun i j=> (hF _ _).2)
    have hv:gross (fun x y:X=> inner ℝ (unionC s R b x) (unionC s R b y)) e= ∑' i,K i:=by simp_rw [← fun x y=> (hF x y).1]; exact hP
    let H(i:ℕ×ℕ):=-2*inner ℝ (v i.fst) (v i.snd); have hH :Summable H:=((thin I hh hh).2.mul_left (-2)); have hz:(∑' i,H i)=-2*inner ℝ (setting e R s b.2) (setting e R s b.2):=by unfold H; rw [tsum_mul_left]; exact congr_arg (-2*·) ((thin I hh hh).1)
    let d(i:ℕ):=|(f i).1| *Real.exp (a*(f i).2.length); have hG:= hp.rows b.2; have hN(i:ℕ): 0 ≤ d i:=hG.1 i
    have hx(i:ℕ×ℕ): |K i-H i| ≤ d i.fst*d i.snd*url n p a:=by
         obtain ⟨i,j⟩:=i; let v':=(f i).1*(f j).1; let u:=(f i).2; let w:=(f j).2; let Z₀:=year e s I b.1 u w
         have hr (x y): X' (i,j) x y = v' *inner ℝ (curlX s (slotFace u b.1) x) (curlX s (slotFace w b.1) y):=by unfold X' g v'; simp only [real_inner_smul_left,real_inner_smul_right]; change _= _ *inner ℝ _ _; unfold u w;ring
         have H0: K (i,j)=v'*Z₀:=by unfold K Z₀ year gross; simp_rw [hr,mul_assoc]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [Finset.mul_sum];rfl -- volume no
         let D:=-2*inner ℝ (mark u.plaq e s) (mark w.plaq e s); have Hu: H (i,j)=v'*D:=by unfold H v D v' u w; simp only [real_inner_smul_left,real_inner_smul_right]; ring
         rw [H0,Hu,← mul_sub,abs_mul]; apply le_trans (mul_le_mul_of_nonneg_left (routeS (δ:=a) e b.1 s I p ‹_› hE hp.width (by norm_num:0 ≤ (1:ℝ)) (fun x y=>by rw [one_mul]; change |inner ℝ x y| ≤ _; exact abs_real_inner_le_norm _ _) u w (u.length+w.length) (by omega) (by omega)) (abs_nonneg v')) _
         simp only [v',D,d,one_mul,abs_mul, u,w, Nat.cast_add,mul_add,Real.exp_add]; apply le_of_eq; ring
    let Tq(i:ℕ×ℕ):= d i.fst*d i.snd
    have ht : Summable Tq := summable_mul_of_summable_norm (f:=d) (g:=d) hG.2.1.norm hG.2.1.norm
    have htG:∑' i,Tq i ≤ C*C:=by
        have hn:0 ≤ ∑' i,d i:=tsum_nonneg hN; rw [show (∑' i,Tq i)= (∑' i,d i)*(∑' i,d i) from (Summable.tsum_mul_tsum (f:=d) (g:=d) hG.2.1 hG.2.1 ht).symm]; exact mul_le_mul hG.2.2 hG.2.2 hn (hn.trans hG.2.2)
    rw [hv,← hz, ← Summable.tsum_sub hA hH]; refine (norm_tsum_le_tsum_norm (show Summable _ from (hA.sub hH).norm)).trans (((hA.sub hH).norm.tsum_le_tsum hx (ht.mul_right _)).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right htG (spreadR ..)
end YM.MSbar.Midpoint
