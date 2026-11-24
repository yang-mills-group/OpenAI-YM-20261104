import YM.FormalBulk08.Sable.Crow
import YM.FormalBulk08.Quire.Moral

/-! pre & post bills for ksrc contacts. Inc cancellation in Pearl. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels Dawn Palm PowerSeries
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{m d D l u j t r:ℕ} {η A B C:ℝ} {K: KernelChoices}

def Pawn (a: Loc G 1)(u:ℕ)(T: Anthem D G)(e:ℕ) (B:ℝ) := 0≤B ∧ ∀ j<e,∀ r p, Knoxville (grain (fame _) 1) u (0,a) (T p j r) (B*‖p‖)
lemma claspP (F:Frame G d)(o:Loc G 1)(e r l D:ℕ)(h:d*d ≤u):∃ C:ℝ,0≤C∧∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Pawn o u Y e B→ (∀ i:Letter F, ‖coeff e (echo F Y i)‖≤B) → Steps F o u (d+1) e r Y (C*B):= by
    have hp:∃ A:ℝ,0≤A∧∀ Y:Anthem D G, Clef o Y l→∀ B:ℝ,Pawn o u Y e B→∀ p,Steam (Y p e r) u ((A*B)*‖p‖) o:= by
       cases r with
       | zero=>exact ⟨0,le_rfl,fun Y _ _ _ _ _ he=>by omega⟩
       | succ m=> obtain ⟨A,hA,H⟩:=soak e m u (0,o);refine ⟨_,hA,fun Y hy B hb p=>?_⟩;rw [mul_assoc]; exact roofSte (H (Y p) (shells Y hy p) (hy.fare.2.1 p _ _) 1 le_rfl _ (mul_nonneg hb.1 (norm_nonneg _)) (fun j hj i ht he=> hb.2 j hj i p))
    choose X hX HX using fun (v:Letter F)(t:ℕ)=> rent_book F v o t h
    let Z(v:Letter F):=∑ j∈Finset.range r,X v j*‖inside F v D‖; let C:= ∑ v,Z v; have hh(v):0≤Z v:=Finset.sum_nonneg (fun j _=>mul_nonneg (hX ..) (norm_nonneg _)); have hc:0≤C:= Finset.sum_nonneg (fun i _=> hh i)
    obtain ⟨A,hA,H⟩:=hp; let D':=A+(1+C); have hE : A≤D':= le_add_of_nonneg_right (add_nonneg zero_le_one hc)
    refine ⟨_,hA.trans hE,fun Y hy B hb hp=>⟨mul_nonneg (hA.trans hE) hb.1,fun i=>steam_m (H Y hy _ hb i) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hb.1) (norm_nonneg _)),fun i hi _=>?_⟩⟩
    let X:= ∑ j∈Finset.range r,if r-j≤e then pearlJ F (Y (inside F i D) (e-(r-j)) j) (mint F i) else 0
    have he': coeff e (echo F Y i)= X + pearlJ F (Y (inside F i D) e r) (mint F i):=by rw [echoline,hi,Finset.sum_range_succ,Nat.sub_self,if_pos (Nat.zero_le _),Nat.sub_zero]
    rw [show pearlJ F _ _ = _ from (show pearlJ F (Y (inside F i D) e r) _= coeff e (echo F Y i)-X by rw [he',add_sub_cancel_left])]; apply (norm_sub_le ..).trans; refine (add_le_add (hp _) (show ‖X‖≤ C*B from ?_)).trans ?_
    · refine le_trans ?h (mul_le_mul_of_nonneg_right (show Z i≤ C from Finset.single_le_sum (fun i _=>hh i) (Finset.mem_univ i)) hb.1); unfold X; apply (norm_sum_le ..).trans; unfold Z; rw [Finset.sum_mul]; refine Finset.sum_le_sum (fun j hj=>?_); rw [Finset.mem_range] at hj;split
      next he=> apply le_trans (HX i j _ _ (hb.2 _ (by omega) j _)) (le_of_eq ?_);ring
      next=> rw [norm_zero];exact mul_nonneg (mul_nonneg (hX ..) (norm_nonneg _)) hb.1
    have hx:1+C≤ D':= le_add_of_nonneg_left hA; apply le_trans (b:=(1+C)*B) (by rw [add_mul,one_mul]);exact mul_le_mul_of_nonneg_right hx hb.1
lemma runners_chalk (F:Frame G d)(a:Loc G 1)(T S:Tile (edgeL G) m)(h:Knoxville (grain (fame _) 1) u (0,a) T A)(hv:Knoxville (grain (fame _) 1) u (0,a) S B)(i:F.Index)(hs:d*(F.grades i).2≤u) : pearlJ F (T+S) i=pearlJ F T i+pearlJ F S i:= by
   let n:= (F.grades i).2; let H := slate_back a m d n hs; have he: slate (T+S) d n=slate T d n+slate S d n:= by ext1 x; rw [slate_k _ _ _ _ hs (T+S) (h.add hv), _root_.add_apply, slate_k _ _ _ _ hs T h,slate_k _ _ _ _ hs S hv,←Summable.tsum_add (H.choose_spec.2 T A h x).1.of_norm (H.choose_spec.2 S B hv x).1.of_norm]; apply tsum_congr; intro i; rw [Pi.add_apply,add_mul];
   unfold pearlJ;change (pocket _ (slate (T+S) d n) _ _).re= _; rw [he,Pose.bunch];rfl
lemma roadster (a:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(d e r:ℕ)(K:KernelChoices)(T:Anthem D G)(l:ℕ)(ht:Clef a T l)(S C Z:ℝ)(he:(Flight.duo K.penalty P).A0.strip η S)(hc:0≤S)(hz:(locating G K P V).strip η C)(hZ:(roots G K P V).strip η Z)(hs:0<η){B:ℝ}(hb:0≤B)(hu:∀ v,Steam (T v e r) u (B*‖v‖) a)(hL:2≤P.L.val):
     let X := (Fintype.card (Bank.Board G P.patch):ℝ)* (1 *(Fintype.card (BoardL G P.patch V)*(1*max 1 C)))
     let b:=max S (max Z X)
     ∀ f: Studio D, Knoxville (grain (fame _) 1) u (0,a) (blade P K V T d e r hL f-towerV (chair P G K) T d e r hL f) ((P.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)*(b+b)))^r)*B*‖f‖):= by
     intro X b f; unfold blade towerV; rw [←smul_sub,←Finset.sum_sub_distrib]; let W:ℝ:= r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)*(b+b)))^r)
     have hb':0≤b:=hc.trans (le_max_left ..); have hh := sack_pos u hs; have hw:0≤W:=by unfold W; positivity
     let g x:=throughW x D hL f
     have hj x: Knoxville (grain (fame _) 1) u (0,a) (lowmost P K V x (T (g x) e r)-upmost P.L x (chair P G K) (T (g x) e r)) (W*B*‖f‖):= by
        obtain ⟨A',σ,H,h⟩:=rum T a ht (g x) e r; let v:edgeL G:=(lift x,a); let t:= carries (lift x) (T (g x) e r)
        have hμ (k:ℕ)(hk:r=k+1): Knoxville (grain (fame _) 1) (u:ℝ) v (tap (lengthen hk t)) (B*‖g x‖):= by subst r; change Knoxville _ _ _ (tap t) _;unfold t; rw [tap_shift]; exact fled (lift x) a (hu _ k rfl)
        have hv:= absolution v P V a hs (show (1:ℝ≥0) ≤ P.L.val * (1:ℝ≥0) by rw [mul_one]; exact Nat.one_le_cast.mpr P.L.pos) le_rfl (knight _ a _ h) H (show Agate t from fun v s=> carrying _ s (ht.fare.2.1 _ _ _) v) hμ he hc hz hZ
        rw [show piz P.L v a=(0,a) from chief_h a P _] at hv;apply hv.mono; refine le_trans (le_of_eq (b:=W*B*‖g x‖) ?_) (mul_le_mul_of_nonneg_left (through_le ..) (mul_nonneg hw hb));unfold W b X; dsimp;ring
     apply ((knox_sum Finset.univ (fun x _=>hj x)).smul _).mono;rw [income_by]; apply le_of_eq; unfold W;ring
lemma raiseB (a:Loc G 1)(F:Frame G d)(H:Hol G)(r l e D:ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤t)(hη:0<η)(hc:0≤C)(hs:(d+1)*(d+1)≤u)(K:KernelChoices):
    ∃ X:ℝ,0≤X ∧∀ P:Patch,X≤(P.L.val:ℝ) → ∀ S:Lodge P,∃ W:ℝ,0≤W ∧ ∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ hz:Z.patch=P,hz ▸ U=S → RepeatPrices K.penalty η C Z →
       ∀ T:Anthem D G, Clef a T l→∀ B:ℝ,Pawn a u T e B→(∀ i,‖coeff e (echo F T i)‖ ≤ B) → ∀ A:ℝ,0≤A →(∀ p,Knoxville (grain (fame _) 1) u (0,a) (T p e r) (A*‖p‖))→∀ hL:2≤ Z.L.val,
          (∀ i:Letter F,slots F i=r→‖pearlJ F (blade Z K U T d e r hL (inside F i D)) (mint F i)‖≤ W*B) ∧ (∀ p: Studio D, Knoxville (grain (fame _) 1) u (0,a) (blade Z K U T d e r hL p) ((Dove.Mulct Z.L*A+W*B)*‖p‖)):= by
    obtain ⟨B,Y,hB,hY,Hy⟩:= slol F H a r l D e (d+1) le_rfl hs h hη hc; have h':d*d ≤u:= le_trans (Nat.mul_le_mul (by omega) (by omega)) hs
    obtain ⟨N,hN,HN⟩:=claspP F a e r l D h'; refine ⟨B^2,sq_nonneg _,fun P hK S=>?_⟩
    obtain ⟨A,hA,Hk⟩:= Lodge.bothPay G K S η hη
    let X:= (Fintype.card (Bank.Board G P):ℝ)* (1*(Fintype.card (BoardL G P S)*(1*max 1 (A*C))));let β:=max C (max (A*C) X)
    let p:ℝ:= (P.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η * (Fintype.card (Loc G 1)*(β+β)))^r)*N
    have hβ:0≤β:=hc.trans (le_max_left ..);have hz:= sack_pos u hη; have hh:0≤p:=by unfold p; positivity
    let Q:=p+(P.L.val:ℝ)^d*Y*N; have hQ:0≤Q:=add_nonneg hh (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hY) hN)
    let L:=Finset.univ.filter (fun i:Letter F=>slots F i=r)
    choose! C' hc' K' using fun i:↥L=> endorse a F l r (d+1) e D h le_rfl i.val (Finset.mem_filter.mp i.property).2 (Nat.lt_succ_of_le (weightFits F i.val)) P.L j t (by omega) hj ht H K hs
    choose! A' ha' H' using fun (i:Letter F)=> rent_book F i a r h'
    let w (i:↥L):= C' i*N + A' i.val * (p*‖inside F i.val D‖); let W:=∑ i:↥L,w i; have hw i:0≤w i:= add_nonneg (mul_nonneg (hc' i) hN) (mul_nonneg (ha' i.val) (mul_nonneg hh (norm_nonneg _))); have Hx:0≤W:= Finset.sum_nonneg (fun i _=>hw i)
    refine ⟨W+Q,add_nonneg Hx hQ,fun Z U hR uR hf T hT M hM hz' E hE Ht hL=>?_⟩;subst P;subst S
    have hh:= HN T hT M hM hz'; have Hh:=Dove.gauss_price hf hp; have Hx': (linesOf Z K.penalty).strip η C:= strip_mono (Hh [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..)); have hx:=Hk _ _ hc Hx'
    have hb' : gauss (chair Z G K) η C (d+1):= by intro i hi; unfold Glide.chair; rw [advance_grown]; exact grown_budget G _ (mul_nonneg hc (pow_nonneg (by positivity) _)) (Hh i hi)
    let t:=towerV (chair Z G K) T d e r hL;let b:=blade Z K U T d e r hL
    have he v: Knoxville (grain (fame _) 1) u (0,a) (b v-t v) (p*M*‖v‖):= by
       have he:= roadster a Z U d _ _ K T _ hT _ _ _ Hx' hc hx.1 hx.2.1 hη hh.1 hh.2.1 hL v; apply he.mono; apply le_of_eq; unfold p; change (Z.patch.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card _*(β+β)))^r)*(N*M)*‖v‖= _;ring
    have Hh':= Hy T hT Z.L Z.odd (chair Z G K) hb' (N*M) E hh Ht hE hL
    constructor
    · intro i hi; let v:=inside F i D; let i': ↥L :=⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      have hu' := K' i' Z rfl hL T hT _ hh η C hη Hx' hc
      change ‖pearlJ F (b v) _‖≤_;nth_rw 1 [←sub_add_cancel (b v) (t v)];rw [runners_chalk F a _ _ (he v) (Hh' v) (mint F i) ((Nat.mul_le_mul_left d (slotsFits F i)).trans h')];apply (norm_add_le ..).trans; apply (add_le_add (H' i _ _ (he v)) hu').trans; refine (le_of_eq (b:= w i'*M) ?_).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (f:=w) (fun i _=> hw i) (Finset.mem_univ _)).trans (show W≤ W+Q from le_add_of_nonneg_right hQ)) hM.1); unfold w;change _= (C' _*N + _*(p*‖v‖))*M; ring
    intro v; have hx:= (he v).add (Hh' v);rw [tall_zero, sub_add_cancel (b v) (t v)] at hx;apply hx.mono; have hd:= Dove.adhere hK;refine le_trans (le_of_eq (b:= (B/(Z.L.val:ℝ)*E+Q*M)*‖v‖) ?_) (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hd hE) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left Hx) hM.1)) (norm_nonneg _)); unfold Dawn.scale Q; rw [show Z.patch.L=Z.L from rfl];ring
end YM.FormalBulk08.Sable
