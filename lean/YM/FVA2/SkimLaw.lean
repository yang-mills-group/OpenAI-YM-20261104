import YM.FVA2.Railway
/-!
# Quantitatively forcing grade survival by looking at a large *inverse* length parameter.

 Strictly lower scales vanish there. Any graded PowerLog shape made from filtration-preserving
 action in two bases thus excludes loss of weight. Doesn't require any products with coincident
 supports.
-/
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.FVA2.Ember
open Function Filter Set Finset Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Convolve MS.Book.Program WorldJet Counterpart Clock Real
open Pic -- massW
open PowerSeries
open scoped Topology ContDiff Classical
variable {I J:Type} {G:Gauge} (V:Warehouse G)
local notation "Y"=> V.F
variable (C:Panel V.F)(L: Strat V.F){v:Word ℝ} (s y:ℝ)(k:ℕ){m d:ℕ}(w j:Fin m→BasisIx G d) (p:Polyp m)
local notation "B"=> sameAxis V.F d
-- epsilon.Name.Status.
def Draw (f:Panel V.F) (d n:ℕ)(w:Fin m→ BasisIx G d) (s:ℝ) (x:Polyp m) := (f.swell s).out d x n ( sameAxis V.F d ∘ w)
def plain (A:Panel V.F) := ∀ d m k (w:Fin m→ BasisIx G d), Ready (Draw V A d k w)
def book (k:ℕ)(s:ℝ)(w: Fin m→ BasisIx G d)(x:Polyp m): ℂ:= PayAll.taste ( C.out d ( shiftP s x ) ) ( sameAxis V.F d∘w ) k
private abbrev enter (d k:ℕ)(z:Fin m→BasisIx G d)(s:ℝ): Polyp m→ℂ:= Draw V C d k z s
private def zσ (y:ℝ)(k:ℕ):ℂ:= factor y k
private lemma tσ (s:ℝ)(k:ℕ): zσ (-s) k * zσ s k=1:= by unfold zσ; rw [← Complex.ofReal_mul,factσ ]; simp [ Verne.factor ]
private lemma tσ' (s:ℝ)(k:ℕ): zσ s k * zσ (-s) k=1:= by rw [mul_comm,tσ ]
private lemma fieldCharge : book V C k s w p=zσ (-s) (massW w) * Draw V C d k w s p:= by
    unfold Draw; rw [ Pic.basis_sphere ]; rw [← mul_assoc, show zσ (-s) _ *(factor s (massW w):ℂ)=1 from tσ s (massW w), one_mul ]; rfl
-- polynomial after gauge scale.Need inverse D
private abbrev gene (L:Strat V.F)(w j:Fin m→BasisIx G d) (k:ℕ):ℂ:= PowerSeries.coeff k (rentF V.F (L.wire d) (sameAxis V.F d) j ( sameAxis V.F d ∘ w ))
private abbrev deltaP (i j:ℕ)(x:ℝ):= zσ x i * zσ (-x) j
lemma twistP : Draw V (C.flip L) d k w s p= ∑ i: Fin m→ BasisIx G d,∑ r∈ antidiagonal k, deltaP (massW w) (massW i) s* (gene V L w i r.1 * Draw V C d r.2 i s p ):= by
    rw [ Draw, Pic.basis_sphere ]; unfold Panel.flip; simp only []; simp_rw [repr_h, show ∀ v (p:Polyp m) (i:ℕ), C.out d (shiftP s p) i ( sameAxis V.F d ∘ v )=_ from fun v p i=> fieldCharge V C s i v p ]; unfold deltaP; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=>?_ ; change zσ s (massW w)* ( gene V L w i _ * _) =_ ; ring -- opacity
--lemma cut0 (f:L.World):f=f:=rfl -- remove
-- projection of price moments.No rank restriction. only from Frame B.
private lemma glyphP (P:Strat V.F)(p q:BasisIx G d)(i:ℕ): PowerSeries.coeff i (style V.F (P.wire d) B q ( B p ))= (B).coord q ( bufferL V.F ( P.wire d i ) ( B p )) + if p=q∧i=0 then 1 else 0 := by
    rw [ ← Clock.out_coeff, WorldJet.node4, frameWord, LinearMap.add_apply,map_add ]; unfold topD; split <;> rename_i h; · by_cases he:p=q <;> simp [Module.Basis.coord_apply,h,he]; -- maybe rw order
    simp [h]
private lemma stake (w j: Fin m→ BasisIx G d)(h:gene V L w j k≠0)(i:Fin m): (j i).size ≤ (w i).size:= by
    let S(v:BasisIx G d): PowerSeries ℂ:= style V.F ( L.wire d ) B v ( B ( w i ) );
    have he : S ( j i ) ≠ 0:= by
       intro hv; apply h; unfold gene; rw [ WorldJet.real, Finset.prod_eq_zero ( Finset.mem_univ i ) hv , map_zero ];
    by_contra hi; apply he; apply PowerSeries.ext; intro l; have hv:w i ≠ j i:=fun h=>hi (h ▸ le_rfl); rw [show S (j i)=_ from rfl]; unfold S; rw [ glyphP, triangular0 V.F _ _ _ ( lt_of_not_ge hi ), map_zero ]; simp [hv]
private lemma agreed (L:Strat V.F)(p q:BasisIx G d)(i:ℕ)(h:p.size=q.size): PowerSeries.coeff i (style V.F ((only L).wire d) B q ( B p ))= PowerSeries.coeff i (style V.F ( L.wire d ) B q ( B p )):= by rw [ glyphP,glyphP, only_wire, Function.comp_apply,coordDown,if_pos h.symm ]
private lemma zeroed (L:Strat V.F)(p q:BasisIx G d)(he:p.size≠q.size): style V.F ((only L).wire d) B q (B p)=0:= PowerSeries.ext fun n=> by rw [glyphP,only_wire,Function.comp_apply,coordDown,if_neg (Ne.symm he) ]; have h:p≠q:=fun h=> he (h ▸ rfl); simp [h]
private lemma onk (h:∀ a:Fin m,(j a).size=(w a).size): gene V (only L) w j k=gene V L w j k:= by unfold gene; simp_rw [ WorldJet.real,Function.comp_apply ]; congr 1; apply Finset.prod_congr rfl; intro i hi; exact PowerSeries.ext fun n=> agreed V L (w i) (j i) n (h i).symm
private lemma offk (h:¬∀ a:Fin m,(j a).size=(w a).size): gene V (only L) w j k=0:= by
    push Not at h; obtain ⟨i,h⟩:= h; unfold gene; rw [ WorldJet.real,Finset.prod_eq_zero (Finset.mem_univ i) (zeroed V L (w i) (j i) (Ne.symm h) ),map_zero ]
lemma trace (a: Fin m→ BasisIx G d)(t:ℝ): deltaP (massW w) (massW a) t *gene V (only L) w a k=gene V (only L) w a k:= by
    by_cases hx:∀i,(a i).size=(w i).size; · unfold deltaP; rw [show massW a= massW w from Finset.sum_congr rfl (fun i _=>hx i), tσ', one_mul ]
    rw [offk V L k w a hx,mul_zero]
lemma within_price : Draw V (C.flip (only L)) d k w = fun t=> (∑ i: Fin m→ BasisIx G d,∑ j∈ antidiagonal k,gene V (only L) w i j.1 • Draw V C d j.2 i t) := by
    funext t x; rw [twistP ]; simp_rw [ Finset.sum_apply, Pi.smul_apply, smul_eq_mul ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [ ← mul_assoc, trace V L _ w i t ]
-- Helpers.
lemma poly_rot {E:Type}[AddCommGroup E][ Module ℝ E]{P:ℝ→E}(p:Polynomial ℝ) (hp:Ready P): Ready (fun t:ℝ=>P (p.eval t)):= by
    exact Ready.Ind (p:=fun P=>Ready (fun t:ℝ=>P (p.eval t))) hp (fun a v=> (by simpa only [← Polynomial.eval_comp] using ( status (a.comp p) v ))) Ready.zero (fun x y hx hy=> Ready.add_point hx hy) (fun c x hx=> Ready.scale_p hx _ )
lemma smooth_shift {A:ℝ→I→ℂ} (v:ℂ)(h: Ready A): Ready (fun t=>v• (A t)):= (Ready.linear h ( L:=( LinearMap.id (R:=ℂ) (M:= I→ℂ) |> (v • ·) ).restrictScalars ℝ )) -- parsing
lemma shapeM (hp:plain V C) : plain V ( C.flip (only L) ):= by
    intro d m k w; rw [ within_price ]; exact MS.FV2Mod.latSum (E:=Polyp m→ℂ) _ (fun i _=> MS.FV2Mod.latSum _ (fun j _=> smooth_shift _ ( hp .. )))
lemma shapeS (hp:plain V C) : plain V ( C.swell s ):= by intro d m n w; unfold Draw; simp_rw [ swell_steps ]; convert poly_rot (E:=Polyp m→ℂ) ( Polynomial.C s +Polynomial.X ) ( hp d m n w ) using 1; ext; simp [Draw]
--lemma sky : Ready (fun y:ℝ=>fσ y):= by trace_state -- remove
lemma shapeμ (hp:plain V C)(hv:light v): plain V ( C.join v ):= by
    intro d m k w; unfold Draw; simp_rw [Panel.join_scl C _ v hv ]; unfold Panel.join; let G(i:ℕ): ℝ→ Polyp m→ℂ:=fun t x=> ( C.swell t ).out d x i ( sameAxis V.F d ∘ w );
    have hx {K} : Jet.ren (V:=PayAll.hall V.F d m) v K k (sameAxis V.F d ∘ w)= ren v (PayAll.taste K (sameAxis V.F d ∘ w)) k:= congr_fun ( PayAll.value_ren K v (sameAxis V.F d ∘ w)) _ -- p unused
    simp_rw [ hx]; unfold ren Jet.order; let T' :=  OrderedFinpartition k; let J(t:OrderedFinpartition k):=(∏ j, ( ( t.partSize j ).factorial * v ( t.partSize j ):ℝ)) * ((t.length.factorial:ℕ):ℝ); let A(i:ℕ):=( (i.factorial:ℝ) )⁻¹; convert Ready.scale (c:=A k) ( MS.FV2Mod.latSum Finset.univ (F:=fun j t=> J j • G j.length t) (fun j _=> Ready.scale ( c:= J j ) ( hp d m j.length w ))) using 1; ext; simp [G, J,A, Finset.sum_apply,mul_smul ]; -- Pi equality
-- Main theorem grade forcing
private abbrev Decays (f:ℝ→ℂ): Prop:= Tendsto f atTop (𝓝 0)
lemma blaze {Q:ℝ→ℂ}(hQ:Ready Q){x:ℝ}(hx:x<0): Decays (fun s:ℝ=>(Real.exp ( x*s ):ℂ)*Q s):= by
    refine Ready.Ind (p:=fun Q=>Decays (fun s:ℝ=>(Real.exp ( x*s ):ℂ)*Q s)) hQ (fun p v=> ?_) ?_ ?_ ?_; -- base
    · obtain h:= ( Pearl.neg_exp p 0 hx ).mul_const v; simpa only [Alps.amount_mint, zero_add, zero_mul,Complex.real_smul,mul_assoc] using h
    · change Tendsto _ _ _; simp_rw [Pi.zero_apply,mul_zero ]; exact tendsto_const_nhds
    · intro p q a b; simp_rw [ Pi.add_apply, mul_add ]; simpa only [Decays, zero_add] using Tendsto.add a b
    intro c p h; simp_rw [Pi.smul_apply, Complex.real_smul, mul_left_comm _ (c:ℂ) ]; simpa only [Decays, mul_zero] using Tendsto.const_mul (c:ℂ) h -- argument
lemma decid {P:ℝ→ℝ} (h:Ready P)(hz:Tendsto P atTop (𝓝 0)): P=0:= by
    obtain ⟨a,rfl⟩:= h.scalar; rcases lt_or_ge 0 a.degree with ha|ha; · exfalso; exact not_tendsto_atTop_of_tendsto_nhds hz.norm ( a.tendsto_norm_atTop ha ( z:=id ) tendsto_norm_atTop_atTop ); -- exact
    rw [Polynomial.eq_C_of_degree_le_zero ha] at hz ⊢; simp_rw [Polynomial.eval_C ] at hz ⊢; exact funext fun i=> tendsto_nhds_unique tendsto_const_nhds hz
lemma cannot {Q:ℝ→ℂ}(hQ:Ready Q)(hz:Decays Q): Q=0:= by
    have he (L:ℂ→L[ℝ]ℝ) : L ∘ Q=0:= decid ( hQ.linear L.toLinearMap ) (( map_zero L ) ▸ ( L.continuous.continuousAt.tendsto.comp hz )); funext t; apply Complex.ext; exact congr_fun (he Complex.reCLM) t; exact congr_fun (he Complex.imCLM) t
lemma agreement (hc:plain V C) (hp:plain V ( C.flip L )) : Draw V (C.flip (only L)) d k w s p=Draw V (C.flip L) d k w s p:= by
    let Q(t:ℝ):=Draw V (C.flip (only L)) d k w t p; -- syntax
    let f:= fun s:ℝ=> Draw V (C.flip L) d k w s p; let F:=Q - f; let v(a:ℝ→ Polyp m→ℂ)(x):= a x p; let T:( Polyp m→ℂ )→ₗ[ℝ] ℂ:= LinearMap.proj p
    have H:Ready F:= (Ready.linear (shapeM V C L hc d m k w) T).sub ( Ready.linear (hp ..) T ); apply sub_eq_zero.mp ( show F s=0 from congr_fun (cannot H ?_) s );
    unfold F Q f Decays; simp_rw [show ∀x y:ℝ→ℂ, x-y=fun t=>x t-y t from fun _ _=>rfl, twistP,← Finset.sum_sub_distrib ];
    -- establish individual summand ingredient 
    suffices hx : ∀ (i:Fin m→ BasisIx G d)(s r:ℕ), Tendsto (fun y=> deltaP (massW w) (massW i) y * (gene V (only L) w i r * Draw V C d s i y p)-deltaP (massW w) (massW i) y*( gene V L w i r * Draw V C d s i y p )) atTop (𝓝 0) by
        have huu (i:Fin m→ BasisIx G d) := tendsto_finsetSum ( Finset.HasAntidiagonal.antidiagonal k ) (fun j (_:j∈ antidiagonal k)=> hx i j.2 j.1); convert tendsto_finsetSum (Finset.univ) (fun i _=> huu i) using 1; simp
    intro i t r; by_cases he:∀ v:Fin m,(i v).size=(w v).size; · simp_rw [ onk V L r w i he,sub_self ]; exact tendsto_const_nhds
    rw [ offk V L r w i he ]; simp_rw [ zero_mul,mul_zero,zero_sub ]; by_cases H:gene V L w i r=0; · simp only [ H,zero_mul,mul_zero,neg_zero ]; exact tendsto_const_nhds
    have ht : massW i < massW w:= by
        apply Finset.sum_lt_sum (fun j _=> stake V L r w i H j ); push Not at he; obtain ⟨j,he⟩:= he; exact ⟨j,Finset.mem_univ _,lt_of_le_of_ne ( stake V L r w i H j ) he⟩ -- h positions
    let x:ℝ:= (massW i:ℝ)-massW w;
    have ha := blaze ((hc d m t i).linear T) ( x:=x ) (sub_neg_of_lt ( Nat.cast_lt.mpr ht )); have hv (s:ℝ): deltaP (massW w) (massW i) s=(Real.exp (x*s):ℂ):= by unfold deltaP zσ factor; rw [← Complex.ofReal_mul,← Real.exp_add ]; unfold x; congr 2; ring
    have hn := Tendsto.neg ( Tendsto.const_mul (gene V L w i r) ha ); simp only [mul_zero, neg_zero] at hn; simp_rw [hv,mul_left_comm _ (gene V L w i r) ]; exact hn
lemma obstruction (D:(d:ℕ)→Detector V.F d)(hv:C.Fresh)(hl:L.pulse)(h: plain V C)(hp:plain V ( C.flip L )): L.only=L:= by
    apply Panel.final_frame C D hv ( hl.adj L ) hl; nth_rw 1 [ ← Panel.z1 (C.flip (only L)) ]; conv_rhs => rw [← Panel.z1 ( C.flip L )]
    apply Panel.ext; intro d n x; funext k; exact Module.Basis.ext_multilinear (fun _ :Fin n=> sameAxis V.F d) (fun v=> agreement V C L 0 k v x h hp)
end YM.FVA2.Ember
