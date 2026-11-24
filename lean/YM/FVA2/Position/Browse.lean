import YM.FVA2.Position.Lantern
import YM.MS.Mach.Mark
import YM.MS.Theater.Value

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Koszul MS.Motif MS.Arts MS.Garment MS.Halo MS.Mach
open MS.Landau MS.Book MS.Color MS.Lifting
open Analysis Tensor Maxwell Labels MS.Theater
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {G:Gauge} {m n h:ℕ} {x:E4} {z:ℂ} {a b c:Axis}
abbrev Seed (G:Gauge):= ℂ→ Mob G
abbrev Ψ (G:Gauge)(m:ℕ): Sector (Shore G m):= field (Landau.parity (A:=L m) ( C:=G.ColorIndex))
def unavg (G:Gauge)(n h:ℕ): Set (Seed G):={F|∃ (l:Fin n→Plaq) (σ:Grid G n),Pole.wage n l=h ∧ F=Pole.wing n l σ}
def Course (G:Gauge)(n h:ℕ):= Submodule.span ℝ (unavg G n h)
lemma wages (a b:Axis)(j:List Axis)(i:G.ColorIndex): (fun z n=> Pole G n a b z j i)∈ Course G 1 (2+j.length):=by
    refine Submodule.subset_span (Set.mem_setOf.mpr ⟨fun _=>⟨a,b,j⟩, fun _=>i, by simp [Pole.wage,Pole.Grit],funext fun z=> funext fun n=>?_ ⟩); exact Eq.symm (closeAt (p:=Ψ G n) _)
lemma can_p (f: Seed G)(h':f∈ Course G n h): Present f:= by
    refine Submodule.span_induction (p:=fun f _=> Present f) ?_ (Present.here _) (fun i j _ _=> Present.add ) ?_ h'
    · rintro _ ⟨a,i,rfl,rfl⟩; exact Pole.Presence ..
    intro x a hv h; exact Present.smul h (x:ℂ)
def furl (z:ℂ)(x:E4) (a b:Axis): ℕ→ List Axis→Mield G m
 | 0,l=> Pole G m a b z l
 | k+1,l=>∑ j:Axis,x j • furl z x a b k (j::l)
lemma furl_asc (l:List Axis): furl z x a b (n+1) l= ∑ j:Axis,x j • convoke z ( chair m j ) ( furl (G:=G) z x a b n l ):= by
    induction n generalizing l with
    | zero=> rfl
    | succ n ih=> 
        rw [furl,show furl z x a b (n+1) l= ∑ i:Axis,x i • furl (G:=G) (m:=m) z x a b n (i::l) from rfl]; simp_rw [ih, map_sum,show ∀ j i (A: Mield G m), convoke z (chair m j) (x i • A)= x i • convoke z (chair m j) A from fun j i A=> map_smul ((convoke z (chair m j)).restrictScalars ℝ) (x i) A, Finset.smul_sum ]; nth_rw 1 [ Finset.sum_comm ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>smul_comm .. ))
lemma knitted (h:ℕ): graft z a b x h= furl (G:=G) (m:=m) z x a b h []:= by
 induction h with| zero=> rfl| succ k ih=> rw [graft, ih,furl_asc]
lemma furl_rank (h:ℕ)(x:E4)(l:List Axis)(i:G.ColorIndex): (fun z n=> furl (m:=n) z x a b h l i )∈ Course G 1 (2+(l.length+h)):= by
 induction h generalizing l with| zero=> rw [ Nat.add_zero ]; exact wages a b l i| succ k ih=> rw [show (fun (z:ℂ) (n:ℕ)=> furl (G:=G) (m:=n) z x a b (k+1) l i)=∑ j:Axis,x j • (fun z n=>furl (G:=G) (m:=n) z x a b k (j::l) i) from ?_ ]; refine Submodule.sum_mem _ (fun j _=> ?_); apply Submodule.smul_mem; simpa [add_assoc, add_comm k] using ih (j::l); funext z n; simp only [furl,Finset.sum_apply,Pi.smul_apply]
lemma ramp_rank (X:Coord G h): Ramp G h (asC G h X)∈ Course G 1 (h+2):= by
    obtain he:X∈ Submodule.span ℝ (Samples G h):= by rw [ many ]; exact Submodule.mem_top
    refine Submodule.span_induction (p:= fun x _=> Ramp G h (asC G h x)∈Course G 1 (h+2)) ?_ ?_ ?_ ?_ he
    · rintro _ ⟨a,x,c,rfl⟩; rw [show Ramp G h (asC G h (Prong a x c))=(slotDen h)⁻¹ • ∑ i:Axis,x i • (fun (z:ℂ) (n:ℕ)=> furl (G:=G) (m:=n) z x i a h [] c) from ?_]; apply Submodule.smul_mem; exact Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ _ (by simpa only [ List.length_nil,Nat.zero_add,add_comm h] using furl_rank h x (a:=i) [] c)); funext z n; simp only [ ramp_Jrad, Ray,knitted,Pi.smul_apply, Finset.sum_apply ]
    · rw [map_zero,map_zero]; exact Submodule.zero_mem _
    · rintro i j hL hQ hv hV; rw [map_add,map_add]; exact Submodule.add_mem _ hv hV
    rintro x i hi hv; change (( Ramp G h ).restrictScalars ℝ) (asC G h (x • i))∈_; rw [map_smul,map_smul]; exact Submodule.smul_mem _ _ hv
lemma wing_pure (n:ℕ)(l:Fin n→ Plaq)(σ:Grid G n): Pure (Ψ G m) false (Pole.wing n l σ z m):= ( Pole.prepared n l σ).even
lemma course_dark {f:Seed G}(hx:f∈Course G n h): f z m ∈ Dark (Ψ G m):= by
    refine Submodule.span_induction (R:=ℝ) (p:=fun (f:Seed G) _=> f z m∈Dark (Ψ G m)) ?_ (Submodule.zero_mem _) (fun i j h g hf hx=> Submodule.add_mem _ hf hx) (fun c i t h=> Submodule.smul_mem _ (c:ℂ) h) hx; rintro _ ⟨a,x,rfl,rfl⟩; exact wing_pure n a x
abbrev SP (u:Key G) : Coord G u.1:= (Labels.axes G u.1).coord u.2
lemma sampleC (u:Key G) : pick u=asC G u.1 (SP u):= rfl
def Feed (G:Gauge)(m:ℕ)(z:ℂ): Pol G→ₐ[ℂ] Dark (Ψ G m):= MvPolynomial.aeval (fun i:Key G=> (⟨ Ramp G i.1 (pick i) z m,course_dark (ramp_rank (SP i)) ⟩ : Dark ( Ψ G m )))
def seed (G:Gauge) : Pol G→ₗ[ℂ] Seed G where
    toFun p z m:= ( Feed G m z p ).val
    map_add' p q:= funext fun z=> funext fun n=> congr_arg Subtype.val (map_add (Feed G n z) p q)
    map_smul' s p:= funext fun z=> funext fun n=> congr_arg Subtype.val (map_smul (Feed G n z) s p)
local notation "T"=> seed G
local notation "κ"=> Ramp G
lemma seed_x (i:Key G): T (MvPolynomial.X i)= κ i.1 (pick i):= funext fun _=> funext fun _=> congr_arg Subtype.val (MvPolynomial.aeval_X ..)
lemma Vtheta (X:Witness G h): T (page h X)=κ h X:= by
    have he:X=∑ j,X ( Labels.axes G h j ) • pick (G:=G) ⟨h,j⟩:= by apply LinearMap.ext; intro x; let Z:Witness G h→ₗ[ℂ] ℂ:={ toFun f:= f x, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; change X x= Z _; rw [map_sum]; simp_rw [ map_smul ]; exact Theater.re_step x X
    unfold page; conv_rhs=> arg 2; rw [he]
    simp_rw [map_sum,map_smul,LabelC, seed_x]; -- comment
lemma sightC (c:ℂ): T (MvPolynomial.C c)=fun _ n=> coin (A:=Shore G n) c:= funext fun z=> funext fun n=> (congr_arg Subtype.val ( MvPolynomial.aeval_C (R:=ℂ) (f:= fun i:Key G=> (⟨ Ramp G i.1 (pick i) z n,course_dark (ramp_rank (SP i)) ⟩ : Dark ( Ψ G n ))) .. )).trans (cash1 ..)
lemma seed_p (a b:Pol G): T (a*b) z m=bite m G (T a z m) (T b z m):= congr_arg Subtype.val (map_mul (Feed G m z) a b)
lemma stake (a:Pol G): T a 0 0= Theater.orbit G a:= by
   induction a using MvPolynomial.induction_on with
   | C c=> rw [sightC, Theater.cus]
   | add a b ih ht=> simp only [map_add, Pi.add_apply, ih,ht]
   | mul_X a i ih=> rw [seed_p,seed_x,ih, sampleC,ramps_real,Theater.bags,Theater.cusp]; rfl
/-- multiply words - no color yet -/
def multi : Seed G→ₗ[ℝ] Seed G→ₗ[ℝ] Seed G:= LinearMap.mk₂ ℝ (fun a b z n=> bite n G (a z n) (b z n)) (fun i j k=>funext fun z=>funext fun n=>LinearMap.congr_fun (map_add (bite n G) (i z n) (j z n)) (k z n)) (fun z i j=>funext fun p=>funext fun n=> LinearMap.congr_fun (map_smul (bite n G) (z:ℂ) ( i p n )) ( j p n )) (fun i j k=>funext fun z=>funext fun n=>map_add (bite n G (i z n)) (j z n) (k z n)) (fun z i j=>funext fun p=>funext fun n=>map_smul (bite n G (i p n)) (z:ℂ) (j p n))
variable {f p:Pol G} {n k:ℕ}
lemma product_seed (p q:Pol G): T (p*q)=multi (T p) (T q):= funext fun _=> funext fun _=> seed_p ..
lemma prepend (u:Plaq)(i:G.ColorIndex) (l:Fin n→ Plaq)(σ:Grid G n): multi (fun z m=> Pole_leaf (n:=m) z u i) (Pole.wing n l σ)= Pole.wing (n+1) (Fin.cons u l) (Fin.cons i σ) := by
    funext z m
    change bite m G (Pole_leaf z u i) (Pole.wing n l σ z m)= _; change _= bite m G _ (prodS ℂ (bite m G) _ n _)
    simp only [Fin.cons_zero, Function.comp_def,Fin.cons_succ]
lemma ascend (X:Seed G)(u:Plaq)(i:G.ColorIndex)(hX:X∈ Course G n h): multi (fun z m=> Pole_leaf (n:=m) z u i) X ∈ Course G (1+n) (Pole.Grit u+h):= by
    rw [add_comm 1]; let U:= fun z (m:ℕ)=> Pole_leaf (n:=m) z u i; -- n vs m
    suffices he: Course G n h≤Submodule.comap (multi U) ( Course G ( n+1 ) ( Pole.Grit u+h )) from he hX
    apply Submodule.span_le.mpr; rintro _ ⟨l,σ,rfl,rfl⟩; rw [SetLike.mem_coe, Submodule.mem_comap,prepend]; refine Submodule.subset_span (Set.mem_setOf.mpr ⟨_,_,?_,rfl⟩); rw [Pole.wage_add]; rfl
lemma together {f g:Seed G}(hx:f∈Course G 1 k)(hp:g∈Course G n h): multi f g∈Course G (1+n) (k+h):= by
    suffices he: Course G 1 k≤Submodule.comap (multi.flip g) (Course G (1+n) (k+h)) from he hx
    refine Submodule.span_le.mpr ?_; rintro _ ⟨l,σ,rfl,rfl⟩; have he: Pole.wing 1 l σ=(fun z m=> Pole_leaf z (l 0) (σ 0)):= funext fun z=> funext fun m=> closeAt (p:= Ψ G m) _; rw [he,show Pole.wage 1 l=Pole.Grit (l 0) from (by simp [Pole.wage] ) ]; exact ascend g _ _ hp
lemma bymono (e:Key G→₀ℕ)(c:ℝ): T (MvPolynomial.monomial e (c:ℂ))∈ Course G (Finsupp.weight Labels.bidegree e).2 (Finsupp.weight Labels.bidegree e).1:= by
    refine Theater.measureN (fun i p=> T p∈ Course G i.2 i.1) e (c:ℂ) ?_ ?_
    · rw [sightC]; let l:= fun i:Fin 0=> (i.elim0 : Plaq); let x: Grid G 0:= fun i:Fin 0=> i.elim0; have hs : Pole.wing 0 l x∈ Course G 0 0:= Submodule.subset_span (Set.mem_setOf.mpr ⟨l,x,(by simp [Pole.wage]), rfl⟩); rw [show (fun (z:ℂ) m=> (coin (A:=Shore G m) (c:ℂ)))= c • Pole.wing 0 l x from ?_ ]; exact Submodule.smul_mem _ _ hs; funext z m q; rcases q with _|⟨i,l⟩; exact ( mul_one ( c:ℂ ) ).symm; exact (mul_zero (c:ℂ)).symm
    intro x i f hx hh; rw [product_seed,seed_x]; exact together (ramp_rank (SP i)) hh
lemma chooses (p:Pol G)(h0: At p (h,n))(hv:Labels.conjPol p=p): T p∈Course G n h:= by
    have he (e:Key G→₀ℕ): star (p.coeff e) = p.coeff e:= by change starRingEnd ℂ _= _; rw [ ← MvPolynomial.coeff_map (f:= starRingEnd ℂ), show MvPolynomial.map (starRingEnd ℂ) p = p from hv ]
    rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ (fun i hi=>?_); obtain hp:= ( nodeId _ _ ).mp h0 ( MvPolynomial.mem_support_iff.mp hi ); have ht:= bymono i ( p.coeff i ).re; rw [hp,Complex.conj_eq_iff_re.mp (he i)] at ht; exact ht
end YM.FVA2.Position.OpenAxis
