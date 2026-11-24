import YM.X.Wrap.Ply
/-!
# Far census on lifted torus important normalization: ε^-4 per V, ε^4 per voxel. number of lattice weights. After reading SC∗ .
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Porch
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open CellsInt Grow Beamer LiftMark Tensor Rays
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side} {k l m d:ℕ} {R:ℝ} {I:Type*} {G:Gauge} (hq:1<q.val)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable (S: Finset I) (x:I→ Fielding.Walk) (p:I→E4)(hp:∀ i∈ S, plot q (x i) (p i))(χ:Floor R)(H:Apart S p R)
local notation "Q"=> travelers (Prod.fst (β:=Cover) (α:=ℕ)) q G
local notation "B" n=> island q S x p χ n
local notation "L"=> fun i:I=>Meter q Prod.fst (x i) G
variable {i:I}(hi:i∈ S)
local notation "regL" i => side q i
lemma isle_one(a:Lapse)(h:a∈token Prod.fst): a∈ island q S x p χ 0:= Isle.clock h
lemma permits : Allows (token Prod.fst) (island q S x p χ m):= fun f g a c=> by exact (by simpa only [Nat.zero_add] using! (show Isle q S x p χ (0+m) (f*g) from (Isle.clock a).mul c) : Isle q S x p χ m (f*g))
def pillar (q:ℕ+)(k:ℕ)(f:Fan G) : Stella (Hair G) Post:= fun t=> com (tack k (epsilon q t.1) (side q t.1) t.2 f)
include hq hp H hi
lemma window_bird (f:GridF)(hf:f∈bird k): Isle q S x p χ (2+k) (fun t=>((f (regL t.1) t.2 (x i t.1) / (ε t.1)^(2+k):ℝ):ℂ)) := by
    obtain ⟨C,hC,h⟩:= Print.cost hq hf; obtain ⟨c,hc,ht⟩:= fare hq S x p hp χ H hi; let m:=2+k; refine ⟨⟨C*c^m,by positivity,?_⟩,fun {v} hv z hz=>?_ ⟩; swap; · apply Released.lin Complex.ofRealCLM.toLinearMap (glides hq hf (fun he=>hv ⟨i,hi,he.symm⟩) hz (hp i hi))
    filter_upwards [h,ht] with j hj hh z hz hp; let t:= ε j; let n:=regL j; let r:= Print.scale n z (x i j); let a:= f n z (x i j); have he:= hj z (x i j); rw [Complex.norm_real,norm_div,norm_pow]; have ht: 0<t:= epsilon_pos ..; have hy: Width q j z>0:= zero_lt_one.trans_le (depth ..); change ‖a‖ / ‖t‖^m * _ ≤ _;rw [Real.norm_of_nonneg ht.le];
    calc _ ≤ ‖a‖ / t^m * (c*(t*r))^m:= by gcongr; apply hh z hz hp
         _ = ‖a‖*r^m*c^m:= by rw [mul_pow,mul_pow]; field_simp
         _ ≤ _ := by gcongr
lemma pole_cross (f:Fan G)(ht:f∈Reed.grads G k)(u:Stella (Hair G) Post)(h:u∈ Meter q Prod.fst (x i) G): cross Q u (pillar q k f)∈ B 2:= by
    obtain ⟨t,rfl⟩:= h; let F(n:Side)(z y:Cover):= spend n z y f t.x; let h:= window_bird hq S x p hp χ H hi F (enrolled₂ f t.x ht t.order); refine ?_; have he : cross Q (liftC q Prod.fst (x i) t) (pillar q k f)=fun s:Post=> ↑(F (regL s.1) s.2 (x i s.1) / (ε s.1)^(2+(k+t.k))) := ?_; rw [he]; exact Isle.iota 2 (by omega) h
    ext1 ⟨j,z⟩; rw [cross]; unfold liftC pillar; rw [treats_comm, cornered]; apply congr_arg Complex.ofReal; unfold tack; simp_rw [map_smul, ←taste_eval,map_smul]; rw [taste_eval, ← spent]; let a:= ε j; let r:= F (regL j) z (x i j); have hu:0<a:=epsilon_pos ..; change (a^(t.k+1))⁻¹*((a^(k+1))⁻¹*r)=r/a^(2+(k+t.k)); rw [show 2+(k+t.k)= t.k+1+(k+1) by omega,pow_add _ (t.k+1)]; field_simp
omit hq hp H hi
def tower(v:ℕ)(q:ℕ+): Curly G →ₗ[ℂ] Code (Hair G) Post where
    toFun f:=fun t=> epsilon q t.1 ^(-(v:ℤ)) • dress t.2 f;map_add' f g:=by ext1 t; rw [map_add,smul_add];rfl
    map_smul' a f:= by ext1 t; rw [map_smul,smul_comm];rfl
def coal (q:ℕ+)(S: Finset I) (x:I→ Fielding.Walk) (p:I→E4)(χ:Floor R)(v n:ℕ): Submodule ℂ (Curly G):= Submodule.comap (tower v q) (Condition.school (island q S x p χ n) S (travelers Prod.fst q G) (fun i=>Meter q Prod.fst (x i) G))
lemma guild (f:Curly G) : f ∈ coal q S x p χ k l↔Condition (B l) Q S L (tower k q f):= Condition.schools ..
lemma coal_mul (n₁ n₂ k m:ℕ){f g:Curly G}(h:f∈coal q S x p χ n₁ k)(hx:g∈ coal q S x p χ n₂ m): f*g∈ coal q S x p χ (n₁+n₂) (k+m):= by
    rw [guild,show tower (n₁+n₂) q (f*g)=tower n₁ q f * tower n₂ q g from ?_]; exact Condition.campus (fun _ hx _ hy=> Isle.mul (m:=k) (l:=m) hx hy) ((guild S x p χ f).mp h) ((guild S x p χ g).mp hx)
    ext1 a; change epsilon q a.1 ^(-(↑(n₁+n₂):ℤ)) • dress a.2 (f*g)=(epsilon q a.1^(-(n₁:ℤ)) • dress a.2 f) * (epsilon q a.1 ^(-(n₂:ℤ)) • dress a.2 g); rw [map_mul, Nat.cast_add,neg_add,zpow_add₀ (epsilon_pos q _).ne', smul_mul_assoc, mul_smul_comm, smul_smul]
lemma priced_coal (q:ℕ+)(f:Fan G): piece (pillar q k f)= tower (k+1) q (glyph (com f)):= by
    ext1 ⟨v,w⟩; rw [piece]; unfold pillar; dsimp only [Function.comp_apply]; change _= epsilon q v ^(-(↑(k+1):ℤ)) • dress w (glyph (com f)); rw [dress_glyph,com_text,tack,com_text,blade,map_smul,zpow_neg,zpow_natCast];rfl
include hq hp H
lemma coal_unit (f:Fan G)(ht:f∈Reed.grads G k): glyph (com f)∈coal q S x p χ (k+1) 2:= by rw [guild,←priced_coal]; exact Condition.leaves _ (fun i hi v hv=> pole_cross hq S x p hp χ H hi f ht v hv)
lemma coal_x (t:Hair G): MvPolynomial.X (R:=ℂ) t∈ coal q S x p χ 1 2 := by rw [show MvPolynomial.X t= glyph (com (Finsupp.single t 1)) from by rw [com_text,blade,Finsupp.linearCombination_single,one_smul]]; exact coal_unit (k:=0) hq S x p hp χ H _ (by rw [grade0]; simp)
omit hq hp H in
private lemma hint_coal (C₁ C₂:Submodule ℂ (Curly G))(h:∀ f∈C₁,∀ g∈C₁,f*g∈C₂)(hp:∀ i:Hair G,MvPolynomial.X i∈C₁)(s:PlaqAxes)(i j:G.ColorIndex): shiftProduct s i j∈C₂:= by
    unfold shiftProduct; simp only; repeat(first|apply Submodule.sub_mem|apply Submodule.add_mem|apply h|apply hp)
lemma fire_coal (s:PlaqAxes): (vertex s:Curly G)∈ coal q S x p χ 4 6:= by
    rw [trinity]; refine Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ (fun j _=> Submodule.sum_mem _ (fun k _=>?_))); refine Submodule.smul_mem _ _ (coal_mul S x p χ 2 2 2 4 ?_ ?_)
    · rw [faceText, ← com_text]; let a:Address G:=(0,s,i); exact coal_unit (k:=1) hq S x p hp χ H _ (arc_occ a)
    exact hint_coal (coal q S x p χ 1 2) _ (fun _ hh _ hg=> coal_mul S x p χ 1 1 2 2 hh hg) (coal_x hq S x p hp χ H) s _ _
-- far @ all arities
lemma quiet_farm [DecidableEq I] (s:PlaqAxes)(g:I→ Code (Hair G) Post) (hi:Set.InjOn p S)(hg:∀ i∈S,Carries q Prod.fst (x i) (g i)):
   Isle q S x p χ 6 (lap S Q g (tower 4 q (vertex s))):= daylights hq Prod.fst S x p hp hi _ g _ hg (permits S x p χ) ((guild S x p χ _).mp (fire_coal hq S x p hp χ H s)) -- namespace
end YM.PositionX.Crate.Porch
