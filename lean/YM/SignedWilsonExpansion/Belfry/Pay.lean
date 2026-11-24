import YM.SignedWilsonExpansion.Belfry.Shout
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Belfry
open Function Set Filter Asymptotics PowerSeries Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Menus MS.Book MS.Book.Program MS.Book.Convolve MS.Puff MS.Puff.Actors
open XSpace XSpace.Structure1 XSpace.Normalize FVA2 FVA2.Scale FVA2.Reg FVA2.Dframe
open WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.PorchK MarqueQ.Crops MarqueQ.Crops.Taught
open Dancer Commission Belle Belle.Path Belle.Buffet Future
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{ι σ κ κ':Type}{n q m d:ℕ}{L:Filter ι}{θ ε g:ι→ℝ}
namespace ScaleFits
open Generator Generator.Drive
-- all theory.gtn., support algebra estimators. no normed choices.Or.Asio.
variable (h:Tendsto θ L (𝓝 0)) {F K K':ι→Guard G d}{p:ι→ Cn}
abbrev S' {E:Type*}[AddCommGroup E][Module ℂ E](x:ι→E):= SeatsW.Salary ℂ L 1 x
lemma mulE {x y:ι→FieldEnd G d}(hp:SeatsW.Salary ℂ L g x)(v:S' (L:=L) y): SeatsW.Salary ℂ L g (fun i=> x i*y i):=by
    let b:= Module.finBasis ℂ (FieldEnd G d); intro a; have H(i):a (x i*y i)=∑ j,b.coord j (x i)*a ( b j*y i ):=by
       nth_rw 1 [← b.sum_repr (x i),Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_mul_assoc,map_smul]; rfl
    simp_rw[H]; apply IsBigO.sum; intro j _; exact ((hp _).mul (v (a ∘ₗ LinearMap.mulLeft ℂ (b j)))).congr_right (fun i=> mul_one _)
lemma dueRight {x y:ι→ FieldEnd G d}(h:SeatsW.Discount ℂ L ε y)(v:S' (L:=L) x): SeatsW.Discount ℂ L ε (fun i=> x i*y i):=by
     let b:= Module.finBasis ℂ (FieldEnd G d); intro a; have H(i):a (x i*y i)=∑ j,b.coord j (x i)*a ( b j*y i ):=by nth_rw 1 [← b.sum_repr (x i),Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_mul_assoc,map_smul]; rfl
     simp_rw [H]; apply IsLittleO.sum; intro j _; exact ((v _).mul_isLittleO (h (a ∘ₗ LinearMap.mulLeft ℂ (b j)))).congr_right (fun i=>one_mul _)
lemma dueLeft {x y:ι→ FieldEnd G d}(h:SeatsW.Discount ℂ L ε x)(v:S' (L:=L) y): SeatsW.Discount ℂ L ε (fun i=> x i*y i):=by
     let b:= Module.finBasis ℂ (FieldEnd G d); intro a; have H(i):a (x i*y i)=∑ j,b.coord j (x i)*a ( b j*y i ):=by nth_rw 1 [← b.sum_repr (x i),Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_mul_assoc,map_smul]; rfl
     simp_rw [H]; apply IsLittleO.sum; intro j _; exact ((h _).mul_isBigO (v (a ∘ₗ LinearMap.mulLeft ℂ (b j)))).congr_right (fun i=>mul_one _)
lemma Budget.mul (f:Budget L F)(k:Budget L K): Budget L (fun i=>F i*K i):= by
    intro v' t; simp_rw [coeff_mul,map_sum]; refine IsBigO.sum fun v _=> mulE ( f v.1 ) ( k v.2 ) t
lemma B_salary (p:ι→Guard G d)(a:Module.Dual ℂ (FieldEnd G d))(v:Budget L p): funds L (fun i=> Drive.pairing a (p i) ):=by
    intro n; simp_rw [Drive.pairing, coeff_mk]; exact v n a
lemma FO.const {E:Type}[Norm E](x:E) (l:Filter ι): FO l (fun _=>x):= isBigO_const_const _ one_ne_zero _
lemma FO.mul {f g:ι→ℂ}(p:FO L f)(v:FO L g):FO L (fun i=>f i*g i):=( IsBigO.mul p v ).congr_right (fun i=> one_mul _) -- circular?
lemma funds.mul {x y:ι→ Cn}(p:funds L x)(v:funds L y): funds L (fun i=> x i*y i):=by intro j; simp_rw [coeff_mul]; exact IsBigO.sum fun z _=> FO.mul (p z.1) (v z.2)
lemma funds.pow (u:funds L p)(i:ℕ) : funds L (fun j=> (p j)^i):=by
    induction i with
    | zero=> simp_rw [pow_zero]; exact fun i=> FO.const _ _
    | succ i ih=> simp_rw [pow_succ]; exact ih.mul u
lemma funds.subst (u:funds L p) (v:∀ i,Rooted (p i)) {x:ι→Cn}(w:funds L x) : funds L (fun i=>(x i).subst (p i)):=by
     intro i; simp_rw [FPS.coeff_substituted (x _) ((show ∀ i, constantCoeff (p i)=0 from fun i=>(coeff_zero_eq_constantCoeff_apply _).symm.trans (v i)) _)]; apply IsBigO.sum; intro j _; exact FO.mul (w j) (u.pow j i)
lemma Budget.until (y:Budget L F)(u:funds L p)(v:∀ i, Rooted (p i)): Budget L (fun i=> Reg.Point.stepV (p i) (F i)):=by
     intro j x; have hp:= funds.subst u v ( B_salary F x y ) j; simp_rw [show ∀ i, x (coeff j (Reg.Point.stepV (p i) (F i)))= coeff j ( Drive.pairing x ( Reg.Point.stepV (p i) ( F i ) ) ) from fun i=>by simp [Drive.pairing], Drive.cap x _ _ (v _) ]; exact hp
lemma yearParam (T:Guard G d)(x:Module.Dual ℂ (FieldEnd G d))(t:ℝ) : x ( young q t T )= calcT t q (Drive.pairing x T):=by
    unfold young citeS; rw [LinearMap.sum_apply,map_sum,timed]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [LinearMap.smul_apply,map_smul,Drive.pairing, coeff_mk]; exact mul_comm ..
lemma yearP (T:Guard G d)(t:ℝ): young q t T= ∑ i∈ Finset.range (q+1),(t:ℂ)^i • coeff i T:=by unfold young citeS; rw [LinearMap.sum_apply]; rfl
lemma year_convert (T:Guard G d)(t μ:ℝ)(q:ℕ): young q t ( convertT μ T )= Level.turner μ ( young q t T ):= by simp_rw [yearP,map_sum,_root_.map_smul,convertT,coeff_mk]
include h
lemma yearCost (x:Budget L F): S' (L:=L) (fun i=> young q (θ i) (F i)):=by
    intro a; simp_rw [yearParam]; exact Buffet.unfoldW ( amount (q:=q) h (B_salary F a x) ).value
lemma until_paid {x:ι→ℝ}(hx:Audit L θ q p (castℂ x))(u:Budget L F)(v:∀ i,Rooted (p i)): SeatsW.Discount ℂ L (θ^q) (fun i=>young q (x i) (F i)- young q (θ i) ( Reg.Point.stepV ( p i ) (F i) )):=by
     intro a; obtain hp:= Taught.shuffle Buffet.awarded ( low h ) (castℂ θ) castCost hx ( accounts (B_salary F a u) ) (fun i=>(coeff_zero_eq_constantCoeff_apply _).symm.trans (v i)); dsimp only; simp_rw [_root_.map_sub a,yearParam,Drive.cap a _ _ (v _)]; exact soldSc h hp
open XSpace.Normalize
lemma youngster (x:Budget L F)(p:∀ i,Scale.Base (F i)): By ℂ L (fun i=> young q (θ i) (F i)) 1:=by
    intro x'; simp_rw [yearP,map_sum,_root_.map_smul,smul_eq_mul]; let z' (i:ℕ):= if i=0 then x' 1 else 0; rw [show x' 1=∑ i∈Finset.range (q+1),z' i from (by simp [z'])]; refine tendsto_finsetSum _ (fun i _=>?_); by_cases hn:i=0; · subst i; simp only [pow_zero, one_mul, (p _).zero]; exact tendsto_const_nhds
    unfold z'; rw [if_neg hn]; apply (isLittleO_one_iff ℝ).mp
    have hE := ( Wipe.guise ( Wipe.expense h IsEquivalent.refl (Nat.pos_of_ne_zero hn) ) ); simp only [pow_zero,Pi.pow_apply,Complex.ofReal_pow] at hE; exact (IsLittleO.mul_isBigO hE ( x i x' ) ).congr_right fun i=> one_mul _
-- frame step.B.Mass.
lemma yearDifferent {ψ:ι→ℝ}(f: Budget L F)(w:FO L ψ) (u:(ψ-θ)=o[L] ε): SeatsW.Discount ℂ L ε (fun i=> young q (ψ i) (F i)- young q (θ i) ( F i )):=by
     intro x; dsimp only; simp_rw [_root_.map_sub x,yearP,map_sum,_root_.map_smul,smul_eq_mul,←Finset.sum_sub_distrib,←sub_mul]; apply IsLittleO.sum; intro i _
     have he: (castℂ ψ-castℂ θ)=o[L] ε:=( Wipe.guise u ).congr_left fun i=> Complex.ofReal_sub ..
     exact ((Wipe.swing (castℂ ψ) (castℂ θ) (Wipe.earth_p w) (castBound h) he i ).mul_isBigO ( f i x ) ).congr_right (fun i=> mul_one _ )
lemma Fiscal_mul (x:Budget L F)(v:Budget L K) : SeatsW.Discount ℂ L (θ^q) (fun i=> young q (θ i) (F i)*young q (θ i) (K i)-young q (θ i) ( F i*K i )):=by
   let b:= Module.finBasis ℂ (FieldEnd G d); intro a; let f j:= a ∘ₗ LinearMap.mulLeft ℂ (b j); have H (x y:FieldEnd G d): a (x*y)=∑ j,b.coord j x * f j y:=by nth_rw 1 [← b.sum_repr x,Finset.sum_mul,map_sum]; apply Finset.sum_congr rfl; intro k _; rw [smul_mul_assoc,map_smul]; rfl
   have Hp (F K:Guard G d): Drive.pairing a (F*K)=∑ j,Drive.pairing (b.coord j) F*Drive.pairing ( f j ) K:=by
      apply PowerSeries.ext; intro i; simp_rw [Drive.pairing,map_sum, coeff_mk, coeff_mul,map_sum,coeff_mk,H]; rw [Finset.sum_comm]
   dsimp only; simp_rw [_root_.map_sub a,H,yearParam,Hp,map_sum,← Finset.sum_sub_distrib]; apply IsLittleO.sum; intro i _; let Q₁:= fun j=> Drive.pairing (b.coord i) (F j); have he := Taught.mul Buffet.awarded (low h) (castℂ θ) castCost (amount (q:=q) h (B_salary F (b.coord i) x)) ( amount (q:=q) h (B_salary K ( f i ) v) ); rw [one_mul] at he; exact soldSc h he
end ScaleFits
end YM.SignedWilsonExpansion.Belfry
