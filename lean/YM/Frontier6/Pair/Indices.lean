import YM.Frontier6.Pair.Plane
import YM.Frontier6.Pair.GridCapture
import YM.Frontier6.Trajectory.Squad

/-! Tilted-plane costs, inclusive culmination at the reference.
Exponents in this file for the front transport are D-w NOT D. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Filter Lattice Wilson RG Labels Bid Work.G08 Finset Extra.Histories MergeProof MergeProof.Ribbons Next.UVStress
open scoped BigOperators Topology
variable {G:Gauge}(C:Family G){W:Worth}{N p D k : ℕ}
set_option quotPrecheck false
local notation "F"=>C.labels.level D
local notation "V"=>C.factory D N p
local notation "H"=>C.path.levels
local notation "r"=>C.ref D
variable (h:C.Makes)(hc: ColumnSteps C W) (hR:roomCost C.path.levels W) (hb:Bank W C.path.levels) (e:ℕ)(he:e<D)

def voyage (D k n:ℕ) := fee C.path.levels k*(C.S.a (C.ref D) / C.S.a k)^n*(C.path.levels.params (k+1)).columns
lemma voyage_pitch (D n:ℕ) : Note C.S (fun k=> voyage C D k n) n:=by
   exact (((((futon C).powerN 2).mills (((Note.notes _ _ (C.S.a_pos _)).splits (Note.note_a C.S)).powerN n)).mills ((fuNote C).scales C.path.levels.fits.mesh)).swapP (by ring))

include h
lemma raw_reference_pay (hN:k ≤ N) (hk:C.ref D ≤ k) (v:C.label D) :
    let s:= fee C.path.levels k*(C.S.a (C.ref D)/ C.S.a k)^D
    (F).coeffSize v ≤ s*quota C D k N p v:=by
   induction hk with
   | refl=>
      intro s; unfold s; rw [div_self (C.S.a_pos _).ne',one_pow,mul_one]; unfold quota; rw [C.normalized h hN]; exact le_mul_of_one_le_left (size_nonneg ..) (fee_one ..)
   | step hi ih=>
      intro s; rename_i i
      let u:= (V).terminal.symm v; let p':= H|>.params (i+1)
      have hv:= h.calibrated D N p (show r ≤ N from le_trans hi (i.le_succ.trans hN))
      let t j:= fee C.path.levels j*(C.S.a (C.ref D)/C.S.a j)^D
      let L:ℝ:= (C.S.block i).val; let c:= p'.columns; have hc:1≤c:=p'.columns_ge
      have hq:quota C D i N p v ≤ c*L^D*quota C D (i+1) N p v:= hv.front i hi hN u
      have hz : t (i+1)=t i*c^2*L^D:= by
           unfold t; rw [fee_succ,C.S.a_step,div_div_eq_mul_div]; rw [show C.S.a r*_/C.S.a i=C.S.a r/C.S.a i*L by unfold L; ring,mul_pow]; unfold L c p'; ring
      have hu : 0 ≤ t i := mul_nonneg (zero_le_one.trans (fee_one H i)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
      refine (show (F).coeffSize v ≤ t i*quota C D i N p v from ih (i.le_succ.trans hN)).trans ((mul_le_mul_of_nonneg_left hq hu).trans ?_)
      change _ ≤ t (i+1)*_; rw [hz]
      calc _ = t i*c*L^D*quota C D (i+1) N p v:= by ring
           _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show c≤c^2 by simpa using! pow_le_pow_right₀ hc (show 1 ≤ 2 by omega)) hu) (by unfold L; positivity)) (size_nonneg (F) _)

lemma from_whole (hN:k ≤ N) (hk:C.ref D ≤ k) (v:C.label D) : ‖v‖ ≤ voyage C D k D*quota C D k N p v:=by
   refine le_trans ((Push.Local.norm_le_size (F) v).trans (raw_reference_pay C h (p:=p) hN hk v)) ?_
   exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (fee_one ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)) (C.path.levels.params _).columns_ge) (size_nonneg ..)

include hc hR hb he
lemma from_front (hN:k ≤ N) (hk:C.ref D ≤ k) (v:C.label D) :
    ∃ y:C.label D, shed F e ((C.factory D N p).terminal.symm y)=0 ∧ ‖v-y‖≤ voyage C D k (D-(e+1))*quota C D k N p v:=by
    let T:= C.factory D N p; let w:= T.terminal.symm v
    obtain ⟨Z,hZ,hS,hT⟩:= hc D N p (hk.trans hN)
    have hx i (u:F|>.Coeff)(hi:r ≤ i)(ht:i ≤ N) : ((C.factory D N p).entries i u).x=(Z.tone i).index u:=by rw [hZ]; exact (hS.earned i hi ht).currents u
    obtain ⟨y,hy,hq⟩:= yield_plane hS hT hR hb e he w hk hN
    have hr (x) : (Z.tone (C.ref D)).index x=T.terminal x:= (hx _ x le_rfl (hk.trans hN)).symm.trans ((h.calibrated D N p (hk.trans hN)).reads x)
    have hE : (Z.tone (C.ref D)).index (w-y) = v-T.terminal y:= by rw [hr,map_sub,show T.terminal w=v from T.terminal.apply_symm_apply v]
    refine ⟨T.terminal y,by change shed (F) e (T.terminal.symm (T.terminal y))=0; rw [LinearEquiv.symm_apply_apply]; exact hy,?_⟩
    change (F|>.coeffSize ((Z.tone (C.ref D)).index (w-y))) ≤ voyage C D _ _* (F|>.coeffSize ((Z.tone k).index w)) at hq
    rw [hE, ← hx _ _ hk hN] at hq; exact (Push.Local.norm_le_size (F) _).trans hq

lemma legacy_price (hN:C.ref D ≤ N)(v:C.label D) (hv:shed (F) e ((C.factory D N p).terminal.symm v)=0) :
    ‖((C.factory D N p).terminal.symm v)‖≤ fee H N * ((C.S.a N/C.S.a (C.ref D))^(D-e)) * (F|>.coeffSize v):= by
    obtain ⟨Z,hZ,hS,hT⟩:= hc D N p hN
    let w := (C.factory D N p).terminal.symm v
    have hx : (Z.tone (C.ref D)).index w=v:=by
       refine Eq.trans (b:=((C.factory D N p).entries (C.ref D) w).x) ?_ (C.normalized h hN v)
       rw [hZ]; exact ((hS.earned _ le_rfl hN).currents _).symm
    have ht := backwards_top hS hT hR hb e he w hv hN
    -- edit
    simp only at ht; rw [hx] at ht; exact (Push.Local.norm_le_size (F) _).trans ht
end YM.Frontier6.Canvas
