import YM.FormalBulk08.Quire.Tal
import YM.FormalBulk08.Dove.Host

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Quire
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge} {m d D l e r j t n :ℕ}{η σ A B C:ℝ}{P:Patch}{K:KernelChoices}

lemma marks_price (F:Frame G d)(o:Loc G 1)(e r l D:ℕ)(h:2*η<σ)(hs:0≤η):∃ C:ℝ,0≤C∧∀ Y:Anthem D G, Clef o Y l → ∀ B:ℝ,Deposit o σ Y e B → (∀ i:Letter F, ‖coeff e (echo F Y i)‖ ≤ B) → Bonds F o η (d+1) e r Y (C*B):= by
    have hx:0<σ:=by linarith
    have hp:∃ A:ℝ,0≤A ∧∀ Y: Anthem D G,Clef o Y l→∀ B:ℝ,Deposit o σ Y e B→∀ p,Torrid (Y p e r) η ((A*B)*‖p‖) o:= by
       cases r with
       | zero=> exact ⟨0,le_rfl,fun Y _ _ _ _ _ he=>by omega⟩
       | succ m=> obtain ⟨A,hA,H⟩:=marker_print o e m h hs; refine ⟨_,hA,fun Y hy B hb p=> ?_⟩; rw [mul_assoc]; exact current.mpr (H (Y p) (shells Y hy p) (hy.fare.2.1 p _ _) _ (mul_nonneg hb.1 (norm_nonneg _)) (fun j hj i ht he=>hb.2 j hj i p))
    choose X hX HX using fun (v:Letter F)(t:ℕ)=> pearl_cost F o v t hx
    let Z(v:Letter F):= ∑ j∈Finset.range r,X v j*‖inside F v D‖; let C:= ∑ v,Z v; have hh(v):0≤Z v:=Finset.sum_nonneg (fun j _=>mul_nonneg (hX ..) (norm_nonneg _)); have hc:0≤C:= Finset.sum_nonneg (fun i _=>hh i)
    obtain ⟨A,hA,H⟩:=hp; let D':=A + (1+C); have hE : A≤D':= le_add_of_nonneg_right (add_nonneg zero_le_one hc)
    refine ⟨_,hA.trans hE,fun Y hy B hb hp=>⟨mul_nonneg (hA.trans hE) hb.1,fun i=>torrid_mono (H Y hy _ hb i) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hb.1) (norm_nonneg _)),fun i hi _=>?_⟩⟩
    let X:= ∑ j∈Finset.range r, if r-j≤e then pearlJ F (Y (inside F i D) (e-(r-j)) j) (mint F i) else 0
    have he': coeff e (echo F Y i)= X + pearlJ F (Y (inside F i D) e r) (mint F i):=by rw [echoline,hi,Finset.sum_range_succ,Nat.sub_self, if_pos (Nat.zero_le _),Nat.sub_zero]
    rw [show pearlJ F _ _ = _ from (show pearlJ F (Y (inside F i D) e r) _= coeff e (echo F Y i)-X by rw [he',add_sub_cancel_left])]; apply (norm_sub_le ..).trans; refine (add_le_add (hp _) (show ‖X‖≤ C*B from ?_)).trans ?_
    · refine le_trans ?h (mul_le_mul_of_nonneg_right (show Z i≤C from Finset.single_le_sum (fun i _=>hh i) (Finset.mem_univ i)) hb.1); unfold X; apply (norm_sum_le ..).trans; unfold Z; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun j hj=>?_); rw [Finset.mem_range] at hj;split
      next he=> apply le_trans (HX i j _ _ (hb.2 _ (by omega) j _)) (le_of_eq ?_);ring
      next=> rw [norm_zero];exact mul_nonneg (mul_nonneg (hX ..) (norm_nonneg _)) hb.1
    have hx :1+C≤D':= le_add_of_nonneg_left hA; apply le_trans (b:=(1+C)*B) (by rw [add_mul,one_mul])
    exact mul_le_mul_of_nonneg_right hx hb.1
lemma moral (a:Loc G 1)(F:Frame G d)(H:Hol G)(r l e D :ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤ t)(hs:0<σ)(hη:0<η)(hc:0≤C)(K:KernelChoices):
    ∃ X:ℝ,0≤X ∧ ∀ P:Patch,X ≤ (P.L.val:ℝ) → ∀ S:Lodge P, ∃ W:ℝ,0≤W ∧ ∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ hz:Z.patch=P, hz ▸ U=S → RepeatPrices K.penalty η C Z →
       ∀ T:Anthem D G, Clef a T l → ∀ B:ℝ, Deposit a σ T e B → (∀ i,‖coeff e (echo F T i)‖ ≤ B) → ∀ A:ℝ,0≤A→(∀ p,Knoxville (fame _) σ (0,a) (T p e r) (A*‖p‖))→∀ hL: 2≤ Z.L.val,
          (∀ i:Letter F,slots F i=r → ‖pearlJ F (blade Z K U T d e r hL (inside F i D)) (mint F i)‖≤ W*B) ∧ (∀ p: Studio D, Knoxville (fame _) η (0,a) (blade Z K U T d e r hL p) ((Dove.Mulct Z.L*A+W*B)*‖p‖)):= by
    let s:=σ/4
    have he:2*s<σ:=by unfold s;linarith
    have hv:0<s:= by unfold s;positivity
    have h':s≤σ:= by linarith
    obtain ⟨B,Y,hB,hY,Hy⟩:= oath H F a r l D e (d+1) le_rfl h σ η s C hv h' hη.le hc
    obtain ⟨N,hN,HN⟩:=marks_price F a e r l D he hv.le
    let y:=osc σ r/2; have hy: 0<y:=div_pos (osc_pos _ hs) (by norm_num)
    refine ⟨max (max (B^2) (η/s)) (η*r/y),le_trans (by positivity : 0≤B^2) ((le_max_left ..).trans (le_max_left ..)),fun P hp' S=> ?_⟩
    rw [max_le_iff,max_le_iff] at hp'; obtain ⟨⟨hK,hP⟩,hZ⟩:= hp'; have hz : η ≤ P.L.val*s:=(div_le_iff₀ hv).mp hP; have ht':Threshold σ η r P.L:= (div_le_iff₀ hy).mp hZ
    obtain ⟨A,hA,Hk⟩:= Lodge.bothPay G K S η hη
    let X := (Fintype.card (Bank.Board G P):ℝ) * (1*(Fintype.card (BoardL G P S)*(1*max 1 (A*C))))
    let β:=max C (max (A*C) X)
    let p:ℝ:=(P.L.val:ℝ)^d*r*(Real.exp (8*η)*(Fintype.card (Loc G 1)*(β+β))^r) * N
    have hβ:0≤β:=hc.trans (le_max_left ..);have hh:0≤p:=by unfold p;positivity
    let Q:=p+(P.L.val:ℝ)^d*Y*N; have hQ:0≤Q:=add_nonneg hh (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hY) hN)
    let L:=Finset.univ.filter (fun i:Letter F=>slots F i=r)
    choose! C' hc' K' using fun i:↥L=> inclusive a F l r (d+1) e D h le_rfl i.val (Finset.mem_filter.mp i.property).2 (Nat.lt_succ_of_le (weightFits F i.val)) P.L j t (by omega) hj ht H K hv
    choose! A' ha' H' using fun (i:Letter F)=> pearl_cost F a i r hη
    let w (i:↥L):= C' i*N + A' i.val * (p*‖inside F i.val D‖); let W:= ∑ i:↥L,w i; have hw i:0≤w i:= add_nonneg (mul_nonneg (hc' i) hN) (mul_nonneg (ha' i.val) (mul_nonneg hh (norm_nonneg _))); have Hx:0≤W:=Finset.sum_nonneg (fun i _=>hw i)
    refine ⟨W+Q,add_nonneg Hx hQ, fun Z U hR uR hf T hT M hM hz' E hE Ht hL=>?_⟩; subst P; subst S
    have hh:= HN T hT M hM hz'; have Hh:= Dove.gauss_price hf hp; have Hx' : (linesOf Z K.penalty).strip η C:= strip_mono (Hh [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..)); have hx := Hk _ _ hc Hx'
    have hb' : gauss (chair Z G K) η C (d+1):= by intro i hi; unfold Glide.chair; rw [advance_grown];exact grown_budget G _ (mul_nonneg hc (pow_nonneg (by positivity) _)) (Hh i hi)
    let t:=towerV (chair Z G K) T d e r hL; let b:=blade Z K U T d e r hL;
    have he v: Knoxville (fame _) η (0,a) (b v-t v) (p*M*‖v‖):= by
        have he:= tollgate a Z U d _ _ K T _ hT _ _ _ Hx' hc hx.1 hx.2.1 hη hz hv.le hh.1 (fun v=>penn_shrink (Ht v) h') hh.2.1 hL v; apply he.mono; apply le_of_eq;unfold p; change (Z.patch.L.val:ℝ)^d*r*(Real.exp (8*η)*(Fintype.card _*(β+β))^r)*(N*M)*‖v‖= _; ring
    have Hh':= Hy T hT Z.L Z.odd ht' (chair Z G K) hb' (N*M) E hh Ht hE hL
    constructor
    · intro i hi; let v:=inside F i D; let i': ↥L :=⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      have hu' := K' i' Z rfl hL T hT _ hh (fun v=> ⟨_,penn_shrink (Ht v) h'⟩) η C hη hz Hx' hc
      change ‖pearlJ F (b v) _‖≤_;nth_rw 1 [← sub_add_cancel (b v) (t v)]; rw [chalk F _ _ (he v) (Hh' v) hη hη]; apply (norm_add_le ..).trans; apply (add_le_add (H' i _ _ (he v)) hu').trans; refine (le_of_eq (b:= w i'*M) ?_).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (f:=w) (fun i _=> hw i) (Finset.mem_univ _)).trans (show W≤ W+Q from le_add_of_nonneg_right hQ)) hM.1); unfold w;change _= (C' _*N + _*(p*‖v‖))*M; ring
    intro v; have hx:= (he v).add (Hh' v); rw [tall_zero, sub_add_cancel (b v) (t v)] at hx; apply hx.mono; have hd := Dove.adhere hK; refine le_trans (le_of_eq (b:= (B/(Z.L.val:ℝ)*E+Q*M)*‖v‖) ?_) (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hd hE) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left Hx) hM.1)) (norm_nonneg _)); unfold Dawn.scale Q; rw [show Z.patch.L=Z.L from rfl];ring
end YM.FormalBulk08.Quire
