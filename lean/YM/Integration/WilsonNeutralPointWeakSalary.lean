import YM.Integration.WilsonNeutralPointCourse
import YM.Integration.WilsonNeutralPointSalary
import YM.FormalBulk08.Sable.Skip

/-! The polynomial support moment on a particular affine child, with its own original projected row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointWeakSalary
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Next.Foundations
open Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open Sable WilsonNeutralPointSalary
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{m d D l e r j t n u :ℕ}{η C:ℝ}{L:Side}{a:Loc G 1}{K:KernelChoices}

theorem width (F:Frame G d)(H:Hol G)(a:Loc G 1)(m l D e q:ℕ)(hq:q≤d+1)
    (hp:(d+1)*(d+1)≤u)(hD:d+1≤D)(hs:0<η)(hc:0≤C):
    ∃ X Y:ℝ,0≤X ∧ 0≤Y∧∀ T:Anthem D G,Clef a T l→∀ L:Side,Odd L.val→
      ∀ S:Cross L (Loc G 1) (Loc G 1),gauss S η C q→∀ A C':ℝ,
      Steps F a u q e m T A→(∀ p,Knoxville (grain (fame _) 1) u (0,a) (T p e m) (C'*‖p‖))→
      0≤C'→∀ x:Site L,∀ hL:2≤L.val,∀ f:Studio D,
      Knoxville (grain (fame _) 1) u (0,a) (WilsonNeutralPointSalary.horizontal S T d e m x hL f)
        ((heightK L d q*X*C'+(L.val:ℝ)^d*Y*A)*‖f‖):=by
  obtain ⟨X,Y,hX,hY,order⟩:=skates F H a m l D e q hq hp hD hs hc
  refine ⟨X,Y,hX,hY,fun T ht L odd S hv A M lean spent hM x hL f=>?_⟩
  apply ((order T ht L odd S hv A M lean spent hM x hL f).smul ((L.val:ℝ)^d)).mono
  apply le_of_eq
  rw [abs_of_nonneg (show 0≤(L.val:ℝ)^d by positivity)]
  unfold heightK;ring

theorem mismatch (a:Loc G 1)(P:Flight j t)(V:Lodge P.patch)(d e r:ℕ)(K:KernelChoices)(T:Anthem D G)(l:ℕ)(ht:Clef a T l)(S C Z:ℝ)(he:(Flight.duo K.penalty P).A0.strip η S)(hc:0≤S)(hz:(locating G K P V).strip η C)(hZ:(roots G K P V).strip η Z)(hs:0<η){B:ℝ}(hb:0≤B)(hu:∀ v,Steam (T v e r) u (B*‖v‖) a)(hL:2≤P.L.val):
     let X := (Fintype.card (Bank.Board G P.patch):ℝ)* (1 *(Fintype.card (BoardL G P.patch V)*(1*max 1 C)))
     let b:=max S (max Z X)
     ∀ digit:Site P.L,∀ f: Studio D, Knoxville (grain (fame _) 1) u (0,a) (land P K V T d e r digit hL f-WilsonNeutralPointSalary.horizontal (chair P G K) T d e r digit hL f) ((P.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)*(b+b)))^r)*B*‖f‖):= by
     intro X b digit f; unfold land WilsonNeutralPointSalary.horizontal; rw [←smul_sub]; let W:ℝ:= r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card (Loc G 1)*(b+b)))^r)
     have hb':0≤b:=hc.trans (le_max_left ..); have hh := sack_pos u hs; have hw:0≤W:=by unfold W; positivity
     let g x:=throughW x D hL f
     have hj x: Knoxville (grain (fame _) 1) u (0,a) (lowmost P K V x (T (g x) e r)-upmost P.L x (chair P G K) (T (g x) e r)) (W*B*‖f‖):= by
        obtain ⟨A',σ,H,h⟩:=rum T a ht (g x) e r; let v:edgeL G:=(lift x,a); let t:= carries (lift x) (T (g x) e r)
        have hμ (k:ℕ)(hk:r=k+1): Knoxville (grain (fame _) 1) (u:ℝ) v (tap (lengthen hk t)) (B*‖g x‖):= by subst r; change Knoxville _ _ _ (tap t) _;unfold t; rw [tap_shift]; exact fled (lift x) a (hu _ k rfl)
        have hv:= absolution v P V a hs (show (1:ℝ≥0) ≤ P.L.val * (1:ℝ≥0) by rw [mul_one]; exact Nat.one_le_cast.mpr P.L.pos) le_rfl (knight _ a _ h) H (show Agate t from fun v s=> carrying _ s (ht.fare.2.1 _ _ _) v) hμ he hc hz hZ
        rw [show piz P.L v a=(0,a) from chief_h a P _] at hv;apply hv.mono; refine le_trans (le_of_eq (b:=W*B*‖g x‖) ?_) (mul_le_mul_of_nonneg_left (through_le ..) (mul_nonneg hw hb));unfold W b X; dsimp;ring
     apply ((hj digit).smul ((P.L.val:ℝ)^d)).mono;rw [abs_of_nonneg (show 0≤(P.L.val:ℝ)^d by positivity)]; apply le_of_eq; unfold W;ring
theorem column (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)
    (i:Letter F)(hz:slots F i=n)(hx:Pose.weight F i<q)(U:Side)(j t:ℕ)(hd:d≤j)
    (hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:(d+1)*(d+1)≤u):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ x:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,
      Clef o Y l→∀ B:ℝ,Steps F o u q e n Y B→∀ η A:ℝ,0<η→
      (linesOf P K.penalty).strip η A→0≤A→
      ‖pearlJ F (WilsonNeutralPointSalary.horizontal (chair P G K) Y d e n x hL (inside F i D)) (mint F i)‖≤C*B:=by
  obtain ⟨C,hC,paid⟩:=credulous o F l n q e D hp hq i hz hx U j t hd hj ht H K hs
  refine ⟨(U.val:ℝ)^d*C,by positivity,fun P he x hL Y hY B hB η A hη hX hA=>?_⟩
  obtain ⟨s,A',hs',-,ht'⟩:=hY.fare.2.2 e n
  have hspos : 0 ≤ s := hs'.le
  have strip : (chair P G K).strip (min η s) A := strip_mono (grown_budget G _ hA hX) (min_le_left η s) le_rfl
  have H:=(upheave (o:=o) _ x strip
    hA ((min_le_right η s).trans (zesp hspos)) (lt_min hη hs').le (ht' (throughW x D hL (inside F i D))))
  rw [WilsonNeutralPointSalary.horizontal,chalk_amp F _ H (lt_min hη hs'),_root_.norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (show 0≤(P.L.val:ℝ)^d by positivity)]
  apply (mul_le_mul_of_nonneg_left (paid P he x hL Y hY _ hB _ _ hη hX hA)
    (pow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [he,mul_assoc]

theorem purchase (a:Loc G 1)(F:Frame G d)(H:Hol G)(r l e D:ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤t)(hη:0<η)(hc:0≤C)(hs:(d+1)*(d+1)≤u)(K:KernelChoices):
    ∃ X:ℝ,0≤X ∧∀ P:Patch,X≤(P.L.val:ℝ) → ∀ S:Lodge P,∃ W:ℝ,0≤W ∧ ∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ hz:Z.patch=P,hz ▸ U=S → RepeatPrices K.penalty η C Z →
       ∀ T:Anthem D G, Clef a T l→∀ B:ℝ,Pawn a u T e B→(∀ i,‖coeff e (echo F T i)‖ ≤ B) → ∀ A:ℝ,0≤A →(∀ p,Knoxville (grain (fame _) 1) u (0,a) (T p e r) (A*‖p‖))→∀ digit:Site Z.L,∀ hL:2≤ Z.L.val,
          (∀ i:Letter F,slots F i=r→‖pearlJ F (land Z K U T d e r digit hL (inside F i D)) (mint F i)‖≤ W*B) ∧ (∀ p: Studio D, Knoxville (grain (fame _) 1) u (0,a) (land Z K U T d e r digit hL p) ((Dove.Mulct Z.L*A+W*B)*‖p‖)):= by
    obtain ⟨B,Y,hB,hY,Hy⟩:= width F H a r l D e (d+1) le_rfl hs h hη hc; have h':d*d ≤u:= le_trans (Nat.mul_le_mul (by omega) (by omega)) hs
    obtain ⟨N,hN,HN⟩:=claspP F a e r l D h'; refine ⟨B^2,sq_nonneg _,fun P hK S=>?_⟩
    obtain ⟨A,hA,Hk⟩:= Lodge.bothPay G K S η hη
    let X:= (Fintype.card (Bank.Board G P):ℝ)* (1*(Fintype.card (BoardL G P S)*(1*max 1 (A*C))));let β:=max C (max (A*C) X)
    let p:ℝ:= (P.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η * (Fintype.card (Loc G 1)*(β+β)))^r)*N
    have hβ:0≤β:=hc.trans (le_max_left ..);have hz:= sack_pos u hη; have hh:0≤p:=by unfold p; positivity
    let Q:=p+(P.L.val:ℝ)^d*Y*N; have hQ:0≤Q:=add_nonneg hh (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hY) hN)
    let L:=Finset.univ.filter (fun i:Letter F=>slots F i=r)
    choose! C' hc' K' using fun i:↥L=> column a F l r (d+1) e D h le_rfl i.val (Finset.mem_filter.mp i.property).2 (Nat.lt_succ_of_le (weightFits F i.val)) P.L j t (by omega) hj ht H K hs
    choose! A' ha' H' using fun (i:Letter F)=> rent_book F i a r h'
    let w (i:↥L):= C' i*N + A' i.val * (p*‖inside F i.val D‖); let W:=∑ i:↥L,w i; have hw i:0≤w i:= add_nonneg (mul_nonneg (hc' i) hN) (mul_nonneg (ha' i.val) (mul_nonneg hh (norm_nonneg _))); have Hx:0≤W:= Finset.sum_nonneg (fun i _=>hw i)
    refine ⟨W+Q,add_nonneg Hx hQ,fun Z U hR uR hf T hT M hM hz' E hE Ht digit hL=>?_⟩;subst P;subst S
    have hh:= HN T hT M hM hz'; have Hh:=Dove.gauss_price hf hp; have Hx': (linesOf Z K.penalty).strip η C:= strip_mono (Hh [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..)); have hx:=Hk _ _ hc Hx'
    have hb' : gauss (chair Z G K) η C (d+1):= by intro i hi; unfold Glide.chair; rw [advance_grown]; exact grown_budget G _ (mul_nonneg hc (pow_nonneg (by positivity) _)) (Hh i hi)
    let t:=WilsonNeutralPointSalary.horizontal (chair Z G K) T d e r digit hL;let b:=land Z K U T d e r digit hL
    have he v: Knoxville (grain (fame _) 1) u (0,a) (b v-t v) (p*M*‖v‖):= by
       have he:= mismatch a Z U d _ _ K T _ hT _ _ _ Hx' hc hx.1 hx.2.1 hη hh.1 hh.2.1 hL digit v; apply he.mono; apply le_of_eq; unfold p; change (Z.patch.L.val:ℝ)^d*r*(Real.exp ((u:ℝ)*plum 1 8)*(sack u η*(Fintype.card _*(β+β)))^r)*(N*M)*‖v‖= _;ring
    have Hh':= Hy T hT Z.L Z.odd (chair Z G K) hb' (N*M) E hh Ht hE digit hL
    constructor
    · intro i hi; let v:=inside F i D; let i': ↥L :=⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      have hu' := K' i' Z rfl digit hL T hT _ hh η C hη Hx' hc
      change ‖pearlJ F (b v) _‖≤_;nth_rw 1 [←sub_add_cancel (b v) (t v)];rw [runners_chalk F a _ _ (he v) (Hh' v) (mint F i) ((Nat.mul_le_mul_left d (slotsFits F i)).trans h')];apply (norm_add_le ..).trans; apply (add_le_add (H' i _ _ (he v)) hu').trans; refine (le_of_eq (b:= w i'*M) ?_).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (f:=w) (fun i _=> hw i) (Finset.mem_univ _)).trans (show W≤ W+Q from le_add_of_nonneg_right hQ)) hM.1); unfold w;change _= (C' _*N + _*(p*‖v‖))*M; ring
    intro v; have hx:= (he v).add (Hh' v);rw [tall_zero, sub_add_cancel (b v) (t v)] at hx;apply hx.mono; have hd:= Dove.adhere hK;refine le_trans (le_of_eq (b:= (B/(Z.L.val:ℝ)*E+Q*M)*‖v‖) ?_) (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hd hE) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left Hx) hM.1)) (norm_nonneg _)); unfold Dawn.scale Q; rw [show Z.patch.L=Z.L from rfl];ring

end YM.Integration.WilsonNeutralPointWeakSalary
end
