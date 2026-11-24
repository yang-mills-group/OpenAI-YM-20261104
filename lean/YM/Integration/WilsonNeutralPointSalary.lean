import YM.Integration.WilsonNeutralPointCourse
import YM.FormalBulk08.Quire.Moral

/-! The diagonal tariff at each original digit. The proof uses the per-digit
Grail Ward bound and the per-digit Palm projection before their native sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralPointSalary
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Quire Palm Grail Chapel Next.Foundations
open Series Work.F03 Work.F05 Work.F08
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{m d D l e r j t n :ℕ}{σ η θ C:ℝ}{L:Side}{a:Loc G 1}{K:KernelChoices}

def horizontal (S:Cross L (Loc G 1) (Loc G 1))(T:Anthem D G)(d e r:ℕ)
    (x:Site L)(hL:2≤L.val)(f:Studio D):Tile (edgeL G) r:=
  (L.val:ℝ)^d • upmost L x S (T (throughW x D hL f) e r)

def land (P:Flight j t)(K:KernelChoices)(V:Lodge P.patch)(T:Anthem D G)(d e r:ℕ)
    (x:Site P.L)(hL:2≤P.L.val)(f:Studio D):Tile (edgeL G) r:=
  (P.L.val:ℝ)^d • lowmost P K V x (T (throughW x D hL f) e r)

theorem width (H:Hol G)(F:Frame G d)(a:Loc G 1)(m u D e q:ℕ)(hq:q≤d+1)(hD:d+1≤D)(σ η θ C:ℝ)(hθ:0<θ)(hp:θ≤σ)(he:0≤η)(hc:0≤C): ∃ X Y:ℝ,0≤X ∧ 0≤Y ∧ ∀ T:Anthem D G, Clef a T u → ∀ L:Side,Odd L.val → Threshold σ η m L→∀ S:Cross L (Loc G 1) (Loc G 1), gauss S η C q→∀ A C':ℝ,Bonds F a θ q e m T A → (∀ p, Knoxville (fame _) σ (0,a) (T p e m) (C'*‖p‖)) → 0≤C' → ∀ digit:Site L,∀ hL:2≤L.val,∀ f, Knoxville (fame _) η (0,a) (horizontal S T d e m digit hL f) ((heightK L d q * X*C' + (L.val:ℝ)^d*Y*A)*‖f‖) := by
  obtain ⟨X,Y,hX,hY,H⟩:=overcast H F a m u D e q hq hD σ η θ C hθ hp he hc
  refine ⟨X,Y,hX,hY,fun T ht L ho hW S hs A B ha hz hB x hL f=>?_⟩
  apply ((H T ht L ho hW S hs A B ha hz hB x hL f).smul ((L.val:ℝ)^d)).mono
  apply le_of_eq
  rw [abs_of_nonneg (show 0≤(L.val:ℝ)^d by positivity)]
  unfold heightK
  ring

theorem mismatch (a:Loc G 1)(P: Flight j t)(V:Lodge P.patch)(d e r:ℕ)(K:KernelChoices)(T:Anthem D G)(u:ℕ)(ht: Clef a T u)(S C Z:ℝ)(he:(Flight.duo K.penalty P).A0.strip η S)(hc:0≤S)(hz:(locating G K P V).strip η C)(hZ:(roots G K P V).strip η Z)(hs:0<η)(hp:η≤P.L.val * θ)(hh:0≤θ){A B:ℝ}(hb:0≤B)(hx:∀ v, Knoxville (fame _) θ (0,a) (T v e r) (A * ‖v‖))(hu:∀ v,Torrid (T v e r) θ (B*‖v‖) a)(hL:2≤P.L.val):
    let X := (Fintype.card (Bank.Board G P.patch):ℝ)* (1 *(Fintype.card (BoardL G P.patch V)*(1*max 1 C)))
    let b:=max S (max Z X)
    ∀ digit:Site P.L,∀ f: Studio D, Knoxville (fame _) η (0,a) (land P K V T d e r digit hL f-horizontal (chair P G K) T d e r digit hL f) ((P.L.val:ℝ)^d*r*(Real.exp (8*η)*(Fintype.card (Loc G 1)*(b+b))^r)*B*‖f‖):= by
    intro X b digit f; unfold land horizontal; rw [←smul_sub];let W:ℝ:=r*(Real.exp (8*η)*(Fintype.card (Loc G 1)*(b+b))^r)
    have hb': 0≤b := hc.trans (le_max_left ..); have hw:0≤W := by unfold W; positivity
    let g x:= throughW x D hL f
    have he' x: Knoxville (fame _) η (0,a) (lowmost P K V x (T (g x) e r)- upmost P.L x (chair P G K) (T (g x) e r)) (W*B*‖f‖):= by
       have hg:=uranic a P V x hs hp hh (hx (g x)) (ht.fare.2.1 (g x) _ _) (hu (g x)) he hc hz hZ
       apply hg.mono; refine le_trans (le_of_eq (b:= W*B*‖g x‖) ?_) (mul_le_mul_of_nonneg_left (Dawn.through_le x hL f) (mul_nonneg hw hb)); unfold W b X; dsimp; ring
    apply ((he' digit).smul ((P.L.val:ℝ)^d)).mono
    apply le_of_eq
    rw [abs_of_nonneg (show 0≤(P.L.val:ℝ)^d by positivity)]
    unfold W
    ring

theorem column (o:Loc G 1)(F:Frame G d)(l n q e D:ℕ)(hp:d<D)(hq:q≤d+1)(i:Letter F)(hz: slots F i=n)(hx:Pose.weight F i< q)(U:Side)(j t:ℕ)(hd:d≤j)(hj:4≤j)(ht:4≤t)(H:Hol G)(K:KernelChoices)(hs:0<σ):
    ∃ C:ℝ,0≤C∧∀ P:Flight j t,P.L=U→∀ digit:Site P.L,∀ hL:2≤P.L.val,∀ Y:Anthem D G,Clef o Y l→∀ B:ℝ,Bonds F o σ q e n Y B →(∀ p:Studio D,∃ Z, Knoxville (fame _) σ (0,o) (Y p e n) Z)→∀ η A:ℝ,0<η → η ≤ P.L.val * σ → (linesOf P K.penalty).strip η A → 0≤A →
     ‖pearlJ F (horizontal (chair P G K) Y d e n digit hL (inside F i D)) (mint F i)‖≤ C*B := by
  obtain ⟨C,hC,h⟩:=counting o F l n q e D hp hq i hz hx U j t hd hj ht H K hs
  refine ⟨(U.val:ℝ)^d*C,by positivity,fun P he x hL Y hY B hB hmass η A hη hw hX hA=>?_⟩
  have mass:=Classical.choose_spec (hmass (throughW x D hL (inside F i D)))
  have strip:(chair P G K).strip η A:=grown_budget G _ hA hX
  have paid:=upheave (o:=o) _ x strip hA hw hη.le mass
  rw [horizontal,chalk_amp F _ paid hη,_root_.norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (show 0≤(P.L.val:ℝ)^d by positivity)]
  apply (mul_le_mul_of_nonneg_left (h P he x hL Y hY _ hB hmass _ _ hη hw hX hA)
    (pow_nonneg (Nat.cast_nonneg _) _)).trans_eq
  rw [he,mul_assoc]

theorem purchase (a:Loc G 1)(F:Frame G d)(H:Hol G)(r l e D :ℕ)(h:d<D)(hj:4≤j)(hp:d+1≤j-2)(ht:4≤ t)(hs:0<σ)(hη:0<η)(hc:0≤C)(K:KernelChoices):
    ∃ X:ℝ,0≤X ∧ ∀ P:Patch,X ≤ (P.L.val:ℝ) → ∀ S:Lodge P, ∃ W:ℝ,0≤W ∧ ∀ Z:Flight j t,∀ U:Lodge Z.patch,∀ hz:Z.patch=P, hz ▸ U=S → RepeatPrices K.penalty η C Z →
       ∀ T:Anthem D G, Clef a T l → ∀ B:ℝ, Deposit a σ T e B → (∀ i,‖coeff e (echo F T i)‖ ≤ B) → ∀ A:ℝ,0≤A→(∀ p,Knoxville (fame _) σ (0,a) (T p e r) (A*‖p‖))→∀ digit:Site Z.L,∀ hL: 2≤ Z.L.val,
          (∀ i:Letter F,slots F i=r → ‖pearlJ F (land Z K U T d e r digit hL (inside F i D)) (mint F i)‖≤ W*B) ∧ (∀ p: Studio D, Knoxville (fame _) η (0,a) (land Z K U T d e r digit hL p) ((Dove.Mulct Z.L*A+W*B)*‖p‖)):= by
    let s:=σ/4
    have he:2*s<σ:=by unfold s;linarith
    have hv:0<s:= by unfold s;positivity
    have h':s≤σ:= by linarith
    obtain ⟨B,Y,hB,hY,Hy⟩:= width H F a r l D e (d+1) le_rfl h σ η s C hv h' hη.le hc
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
    choose! C' hc' K' using fun i:↥L=> column a F l r (d+1) e D h le_rfl i.val (Finset.mem_filter.mp i.property).2 (Nat.lt_succ_of_le (weightFits F i.val)) P.L j t (by omega) hj ht H K hv
    choose! A' ha' H' using fun (i:Letter F)=> pearl_cost F a i r hη
    let w (i:↥L):= C' i*N + A' i.val * (p*‖inside F i.val D‖); let W:= ∑ i:↥L,w i; have hw i:0≤w i:= add_nonneg (mul_nonneg (hc' i) hN) (mul_nonneg (ha' i.val) (mul_nonneg hh (norm_nonneg _))); have Hx:0≤W:=Finset.sum_nonneg (fun i _=>hw i)
    refine ⟨W+Q,add_nonneg Hx hQ, fun Z U hR uR hf T hT M hM hz' E hE Ht digit hL=>?_⟩; subst P; subst S
    have hh:= HN T hT M hM hz'; have Hh:= Dove.gauss_price hf hp; have Hx' : (linesOf Z K.penalty).strip η C:= strip_mono (Hh [] (Nat.zero_le _)) le_rfl (mul_le_of_le_one_right hc (ebb ..)); have hx := Hk _ _ hc Hx'
    have hb' : gauss (chair Z G K) η C (d+1):= by intro i hi; unfold Glide.chair; rw [advance_grown];exact grown_budget G _ (mul_nonneg hc (pow_nonneg (by positivity) _)) (Hh i hi)
    let t:=horizontal (chair Z G K) T d e r digit hL; let b:=land Z K U T d e r digit hL;
    have he v: Knoxville (fame _) η (0,a) (b v-t v) (p*M*‖v‖):= by
        have he:= mismatch a Z U d _ _ K T _ hT _ _ _ Hx' hc hx.1 hx.2.1 hη hz hv.le hh.1 (fun v=>penn_shrink (Ht v) h') hh.2.1 hL digit v; apply he.mono; apply le_of_eq;unfold p; change (Z.patch.L.val:ℝ)^d*r*(Real.exp (8*η)*(Fintype.card _*(β+β))^r)*(N*M)*‖v‖= _; ring
    have Hh':= Hy T hT Z.L Z.odd ht' (chair Z G K) hb' (N*M) E hh Ht hE digit hL
    constructor
    · intro i hi; let v:=inside F i D; let i': ↥L :=⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      have hu' := K' i' Z rfl digit hL T hT _ hh (fun v=> ⟨_,penn_shrink (Ht v) h'⟩) η C hη hz Hx' hc
      change ‖pearlJ F (b v) _‖≤_;nth_rw 1 [← sub_add_cancel (b v) (t v)]; rw [chalk F _ _ (he v) (Hh' v) hη hη]; apply (norm_add_le ..).trans; apply (add_le_add (H' i _ _ (he v)) hu').trans; refine (le_of_eq (b:= w i'*M) ?_).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (f:=w) (fun i _=> hw i) (Finset.mem_univ _)).trans (show W≤ W+Q from le_add_of_nonneg_right hQ)) hM.1); unfold w;change _= (C' _*N + _*(p*‖v‖))*M; ring
    intro v; have hx:= (he v).add (Hh' v); rw [tall_zero, sub_add_cancel (b v) (t v)] at hx; apply hx.mono; have hd := Dove.adhere hK; refine le_trans (le_of_eq (b:= (B/(Z.L.val:ℝ)*E+Q*M)*‖v‖) ?_) (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right hd hE) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left Hx) hM.1)) (norm_nonneg _)); unfold Dawn.scale Q; rw [show Z.patch.L=Z.L from rfl];ring

end YM.Integration.WilsonNeutralPointSalary
end
