import YM.FormalBulk08.Pose.Wise

/-! Sym reality under orientation. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift Reef Series Orb PowerSeries
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {n:Side} {η θ A B : ℝ} {r l d u D:ℕ}
variable (s:Signed)
lemma kcompass (p q:Pap (wire G n))(h:Rite p q s 0) (e r)(w:chain (wire G n) r) : rancho p e r (dart s ∘ w)=rancho q e r w *∏ i,City.banner s (bearing (w i)) := by
   -- Reroute guardian
   let R:=City.arc G s n
   have hp:=h (wire G n) (fun z:Jets.Rays (wire G n)=> z ∘ id) R (fun _ _=>1) rfl (map_zero R) (show ContDiffAt ℝ ω (fun z:Jets.Rays (wire G n)=> z) 0 from contDiffAt_id) R.contDiff.contDiffAt (fun _=> contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by unfold R;rw [City.arc_pull]; ext1 b;simp [Lattice.gauge])
   rw [Bank.pane_letter (City.displayed G s n) R R.contDiff.contDiffAt rfl] at hp
   have he:=congr_arg (PowerSeries.coeff e) hp; rw [Jets.fit_translate] at he; simp only [PowerSeries.coeff_map] at he; change MvPolynomial.rename id _ = Wick.mixRows _ _ at he; rw [MvPolynomial.rename_id_apply] at he
   unfold rancho; rw [he, target, pearl,tsum_fintype,Finset.sum_eq_single w]
   · simp [City.displayed,bearing]
   · intro b _ hb; have he:∃ i,b i≠w i:=Function.ne_iff.mp hb; obtain ⟨i,hi⟩:=he; rw [Finset.prod_eq_zero (Finset.mem_univ i) (show City.displayed _ s n _ _=0 from (show City.displayed G s n (b i) ((dart s ∘ w) i)=0 from Pi.single_eq_of_ne ((darts s).ne (Ne.symm hi)) _)),mul_zero]
   simp
lemma kport {T U: Anthem D G}{a:Loc G 1}(h:Son T U l s)(ht: Wade a T l)(hu:Wade a U l)(p:Dawn.Studio D)(i r)(w:chain (edgeL G) r): let q:=Dawn.froth s D p
    T p i r (dart s ∘ w)=U q i r w *∏ k,City.banner s (bearing (w k)):= by
    intro q;let A:= _root_.YM.FormalBulk08.Kemp.banner l (T p);let B:= _root_.YM.FormalBulk08.Kemp.banner l (U q)
    obtain ⟨η,C,hC,-,H⟩:=ht.2.2 i r; obtain ⟨θ,B',hb,-,H'⟩:=hu.2.2 i r
    refine tendsto_nhds_unique ((sieve_kalm _ (H p) hC.le).1 (dart s ∘ w)) ((((sieve_kalm _ (H' q) hb.le).1 w).mul_const _).congr' ?_)
    refine .of_forall fun n=> ?_
    have hx n:=badge (T p) (ht.1 p) (ht.2.1 p) le_rfl n i r;have hb n:= badge (U q) (hu.1 q) (hu.2.1 q) le_rfl n i r; dsimp only; rw [←hx,←hb, show Lotus.drip n ∘ dart s ∘ w=dart s ∘ (Lotus.drip n ∘ w) from funext fun k=>arc_wrap s n (w k)]; exact (kcompass s (A n) (B n) (h n p) i r (Lotus.drip n ∘ w)).symm
-- bijective anchor direction
lemma canon_dart (x : Cover) (a:Axis)(i:G.ColorIndex): dart s (x,Exterior.coord a,i)=(goingUp s a x, Exterior.coord (s.perm a),i):= by rw [dart,going_spec];simp only [show axisEquiv.symm (Exterior.coord a)=a from axisEquiv.symm_apply_apply _];rfl
lemma dart_bij : Bijective (dart (G:=G) (X:=ℤ) s):= by
    constructor
    · rintro ⟨x,k,v⟩ ⟨y,a,V⟩ h; obtain ⟨b,rfl⟩:=axisEquiv.surjective k; obtain ⟨c,rfl⟩:=axisEquiv.surjective a; change dart s (x,Exterior.coord b,v)=dart s (y,Exterior.coord c,V) at h;rw [canon_dart,canon_dart] at h; have hb:=s.perm.injective (axisEquiv.injective (show _ from congr_arg (fun q:edgeL G=>q.2.1) h))
      subst c; have hv : v=V := congr_arg (fun q:edgeL G=>q.2.2) h; exact Prod.ext ((goingUp s b).injective (congr_arg (fun q:edgeL G=>q.1) h)) (Prod.ext rfl hv)
    rintro ⟨x,b,i⟩; obtain ⟨v,rfl⟩:=axisEquiv.surjective b; obtain ⟨k,rfl⟩:=s.perm.surjective v; obtain ⟨x,rfl⟩:=(goingUp s k).surjective x; exact ⟨(x,Exterior.coord k,i),canon_dart ..⟩
lemma wind_tiers (H:Hol G)(v:chain (edgeL G) r): tier v ∘ turnIn G d s =ᶠ[𝓝 0] (∏ i,City.banner s (bearing (v i))) • tier (dart s ∘ v):= by
   let f (x:edgeL G) := curtain (d:=d) x ∘ (turnIn G d s)
   have he (x:edgeL G) : f x =ᶠ[𝓝 0] City.banner s (bearing x) • curtain (d:=d) (dart s x):= by
      rcases x with ⟨x,b,i⟩; obtain ⟨c,rfl⟩:=axisEquiv.surjective b
      let X:edgeL G:=(x,Exterior.coord c,i); have hz : bearing X=c:=axisEquiv.symm_apply_apply _
      change curtain X ∘ _=ᶠ[𝓝 0] City.banner s (bearing X) • curtain (dart s (x,Exterior.coord c,i)); rw [canon_dart,show bearing _=_ from hz]
      filter_upwards [Film.shade (d:=d) H s (x,c)] with z h
      change Film.lane _ (bearing X) _ i=City.banner s c * curtain _ z
      unfold curtain; rw [hz,show bearing (show edgeL G from (goingUp s c x,Exterior.coord (s.perm c),i))= _ from (show bearing _= s.perm c from axisEquiv.symm_apply_apply _)]
      exact congr_arg (fun u:G.Color=> u i) h
   filter_upwards [eventually_all.mpr fun i=>he (v i)] with z hz; change (∏ i, f (v i) z) = (∏ i,City.banner s (bearing (v i)))*(∏ i,curtain (dart s (v i)) z); rw [←Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _=> hz i
set_option maxHeartbeats 600000 in
lemma wind_slate (H:Hol G) (b:Loc G 1)(T U:Tile (edgeL G) r)(h:∀ v,T (dart s ∘ v)=U v*∏ i,City.banner s (bearing (v i)))(hs:0<η)(ht: Knoxville (fame _) η (0,b) T A)(hv:0<θ)(hx: Knoxville (fame _) θ (0,b) U B)(x: Fin l→Snap G d): slate U d l (turnIn G d s ∘ x)=slate T d l x:= by
    rw [slate_read b U _ hv hx, slate_read b T x hs ht]; let g:=Equiv.ofBijective (dart (G:=G) (X:=ℤ) s) (dart_bij s); rw [←Equiv.tsum_eq (Equiv.arrowCongr (Equiv.refl _) g) (fun u:chain (edgeL G) r=> T u *Tensor.coeff (tier u) l 0 x)]; refine tsum_congr fun v=>?_
    have ht:=DFunLike.congr_fun (Tensor.GermCoeff l (wind_tiers (d:=d) s H v)) x
    have he v : ContDiffAt ℝ (↑l) (tier (d:=d) (r:=r) (G:=G) v) 0:= (tier_diff ..).of_le le_top
    let k:ℝ:=∏ i,City.banner s (bearing (v i))
    have hh := ((slump (turnIn G d s) (he v) x).symm.trans (ht.trans (show Tensor.coeff (k • tier (d:=d) (dart s ∘ v)) _ _ x=k*Tensor.coeff (tier (dart s ∘ v)) _ _ x from DFunLike.congr_fun (Tensor.coeff_smul k (he (dart s ∘ v))) x)))
    let w:=dart s ∘ v
    change U v * _ = T (dart s ∘ v)*Tensor.coeff (tier w) _ _ x; rw [h,mul_assoc]; exact congr_arg (U v *·) hh
end YM.FormalBulk08.Pose
