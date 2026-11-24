import YM.FormalBulk08.Grail.Niche

/-! Newton pricing of anchored kernels at a preimage. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I J V: Type} {r l d u D m: ℕ} {G : Gauge} {P : Reach V}{x:V}{η θ σ A B C :ℝ}

-- anchor shell / fill

def robot (a:V)(T:Tile V m):Tile V (m+1) := fun v=>if v 0=a then T (Fin.tail v) else 0
lemma bot_arm (a:V)(T:Tile V m){P:Reach V}(h:Knoxville P η a T A):Bail P η (robot a T) A:= by
    let f (v:chain V (m+1)):=glitter P η (robot a T) v
    have he : (∑' v,f v)≤ ENNReal.ofReal A:= by
        rw [← Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (m+1)=>V)), ENNReal.tsum_prod',tsum_eq_single a]; swap
        · intro b hb; simp [f,robot,hb,glitter]
        change (∑' i,_ ) ≤ _; simp only [f,Fin.consEquiv_apply,glitter,robot,Fin.cons_zero,↓reduceIte];exact h.2
    refine ⟨h.1,fun i x=> ?_⟩; exact (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective f).trans he
lemma from_gate (x:Cover)(a:I)(T:Tile (Biglot I) m)(p:Grades (Fin m×Axis))(t:chain I m): piles (robot (x,a) (carries x T)) (x,a) t p = ∑' w:cloud m, T (snake 0 t w)*hat p w:= by
    unfold piles rowC robot; simp only [Fin.cons_zero,↓reduceIte,Fin.tail_cons]; apply tsum_congr; intro w;change T (Lotus.tint (-x) ∘ _)*_=_; congr 2; ext i <;> simp [snake]

lemma tale_gate [Fintype I] [Fintype J] {L:Side}(S:Cross L I J)(x:Cover)(a:I)(hs:S.strip η A)(hp:0≤η)(hA:0≤A)(T:Tile (Biglot I) m)(hv:0≤σ)(H:Knoxville (fame _) σ (0,a) T C) : pearl (Chapel.merit S) (carries x T)=∑ i:chain I m,glassTail S (x,a) (robot (x,a) (carries x T)) i:= by
    -- reindexed. m=0 also
    funext v; let u:=snaking (m:=m) (I:=I) x; let K:= carries x T; let f(w:chain (Biglot I) m):= K w*∏ i,Chapel.merit S (w i) (v i)
    have hK: Knoxville (fame _) σ (x,a) K C:= by convert mantle_pay x H using 1; exact Prod.ext (zero_add _).symm rfl
    have hX : Summable f:= lenses (C:=C) _ (fun _=> Chapel.merit S) (fun _=> center_row _ hs hp hA) K (fun w => by
      exact le_trans (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (show 0≤σ*herb (fame _) (x,a) w from mul_nonneg hv (Nat.cast_nonneg _)))) (penn_chill _ hK))
    unfold pearl; rw [← Equiv.tsum_eq u (fun p=> K p*∏ i,Chapel.merit S (p i) (v i))]; change (∑' v,(f ∘ u) v)= _; rw [((u.summable_iff.mpr hX)).tsum_prod,tsum_fintype,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; unfold glassTail; exact tsum_congr fun j=>by simp only [rowC,robot,Fin.cons_zero,↓reduceIte,Fin.tail_cons];rfl

lemma wangle (f g:E4→ℝ)(h:f∈rangeLt ℝ (m+1))(hp:g∈rangeLt ℝ (l+1)) : (f*g)∈ rangeLt ℝ (m+l+1):= by
    let M:= ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ; let v : Fin 2→E4→ℝ:= ![f,g]; let p:= ![m,l];
    have he i:v i∈ rangeLt ℝ (p i+1):= by fin_cases i; exact h;exact hp
    have hv:=multi_band M v p he; rw [show ∑ i,p i=m+l by simp [p,Fin.sum_univ_succ], show (fun x=>M (fun i=>v i x))=f*g from funext fun x=>by simp [M,v,Fin.prod_univ_succ]] at hv;exact hv

def frothP (i:Axis)(k:ℕ)(x:E4):ℝ:=Ring.choose (x i) k
lemma prosper (i:Axis)(k:ℕ): frothP i k∈rangeLt ℝ (k+1):= by
    induction k with
    | zero=> rw [show frothP i 0=fun _=> 1 from funext fun _=>by simp [frothP]]; exact exact_le_band zero_lt_one (exact_constant _)
    | succ k ih=>
       let u(x:E4):=x i-(k:ℝ)
       have hu : u∈rangeLt ℝ (1+1):= Submodule.sub_mem _ (exact_le_band (Nat.lt_succ_self _) (exact_linear (EuclideanSpace.proj i))) (exact_le_band (by omega) (exact_constant _))
       rw [show frothP i (k+1)=(((k:ℝ)+1)⁻¹ • (frothP i k*u)) from funext fun x=> rise_hat ..]; exact Submodule.smul_mem _ _ (wangle (frothP i k) u ih hu)
lemma throng {I : Type}(f:I→E4→ℝ)(b: I→ℕ)(p:Finset I)(he:∀ i∈p,f i∈rangeLt ℝ (b i+1)) : (fun x=> ∏ i∈p, f i x)∈rangeLt ℝ ((∑ i∈p,b i)+1):= by
    induction p using Finset.induction with
    | empty=> simp only [Finset.prod_empty,Finset.sum_empty,zero_add]; exact exact_le_band zero_lt_one (exact_constant _)
    | @insert i P h ih=>simp_rw [Finset.prod_insert h,Finset.sum_insert h]; exact wangle (f i) _ (he i (Finset.mem_insert_self ..)) (ih fun i hi=> he i (Finset.mem_insert_of_mem hi))

def notice (p : Seasons)(x:E4): ℝ:=∏ i:Axis,frothP i (p i) x
lemma notices (p:Seasons): notice p ∈ rangeLt ℝ (upper p+1):=throng _ p Finset.univ (fun i _=> prosper i (p i))
-- hat single type

def horn (p : Seasons)(x:Loc G 1)(z:E4) : Axis→G.Color:=notice p z • (Pi.single (axisEquiv.symm x.1) ((EuclideanSpace.basisFun (hue G) ℝ x.2)))
lemma horns (p : Seasons)(x:Loc G 1) : horn p x∈rangeLt (Axis→G.Color) (upper p+1):= by
    let X: Axis→G.Color:= Pi.single (axisEquiv.symm x.1) (EuclideanSpace.basisFun (hue G) ℝ x.2); exact linear_band ((ContinuousLinearMap.id ℝ ℝ).smulRight X) _ (notices p)
lemma horn_eq (p : Seasons)(x y : Loc G 1)(z:Cover): assigns (horn p x) (z,y)=if x=y then hat p z else 0:= by
    have he : notice p (Place.seat z)=hat p z:=rfl
    unfold assigns horn; rw [he]; simp only [bearing,Pi.smul_apply,PiLp.smul_apply]
    rcases x with ⟨q,v⟩; rcases y with ⟨l,k⟩; by_cases hx:l=q
    · subst l; by_cases h:v=k <;> simp [h,eq_comm];
    simp [Ne.symm hx,hx]

def aster (p:Grades (Fin m × Axis))(i:Fin m) : Seasons:=fun j=>p (i,j)
lemma adder (p:Grades (Fin m×Axis)): upper p=∑ i,upper (aster p i):= Fintype.sum_prod_type ..
lemma aroma (p:Grades (Fin m×Axis))(w:cloud m):hat p w=∏ i,hat (aster p i) (rack w i):=Fintype.prod_prod_type ..
lemma horn_test (x:Cover)(a:Loc G 1)(T:Tile (edgeL G) m)(p:Grades (Fin m×Axis))(t:chain (Loc G 1) m) (h:Knoxville (fame _) η (0,a) T A)(hs:0<η): piles (robot (x,a) (carries x T)) (x,a) t p=tariffs (fun i=> assigns (horn (aster p i) (t i))) T:=by
    rw [from_gate]; symm; let V:=snaking (m:=m) (I:=Loc G 1) 0
    let g i:= assigns (horn (aster p i) (t i)); let f v:=T v *∏ i,g i (v i)
    obtain ⟨C,hC,H⟩:= pays_product g a hs (fun i=>shoulder (horns (aster p i) (t i))); change (∑' i,f i)=_
    rw [←Equiv.tsum_eq V f]; change (∑' i,(f ∘ V) i)=_; rw [((V.summable_iff).mpr ((H T A h).1)).tsum_prod,tsum_eq_single t]; swap
    · intro u hu; obtain ⟨j,hj⟩:=Function.ne_iff.mp hu; refine Eq.trans (tsum_congr ?g) (tsum_zero (α:=ℝ)); intro b; change T _*(∏ i,g i (V (u,b) i))=_; rw [Finset.prod_eq_zero (Finset.mem_univ j) (show g j (V (u,b) j)=0 from (horn_eq ..).trans (if_neg (Ne.symm hj))),mul_zero]
    apply tsum_congr;intro v; change T _* (∏ i, assigns _ _)= _; congr 1; rw [aroma]; apply Finset.prod_congr rfl; intro i _; change assigns _ (0+rack v i,t i)= _; rw [zero_add,horn_eq, if_pos rfl]
end YM.FormalBulk08.Grail
