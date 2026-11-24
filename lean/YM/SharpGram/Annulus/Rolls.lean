import YM.SharpGram.Annulus.Balance

/-!
# Directional prices in physical quotient Schur norms

The single-step OPEN estimates are only on the dimensionful Schur forms
`charge` compared with themselves at the *next length n+1*. We weight every
lower block by `1/dial(k)` for resolving both direction price products. This
absorbs offgrade (which is *not* assumed to vanish or be small), buys iteration
polynomial log-price exactly. Neither orientation nor a relation between
output-frame labels is being ignored: only metric data enters that iteration.
In reconstructing costs the triangular change-of-grading has its own relatively
expensive shears; fully account for them here. Derives from monotonicity the
shear estimate, so the assumed physical step data is only on that single-grade
Schur difference. See below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Lenses Push.FiniteDetection.Free Weak.Portfolio
open scoped Topology ContDiff BigOperators Classical NNReal InnerProductSpace
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)}
variable {F: Final C f S}
local notation "V!"=>F.sector.derivatives
local notation "σ"=>F.room.kernel.spin
variable {d : ℕ}

-- algebraic bills chosen polynorm on a particular log scale, Schur remainder
-- need REAL filtration only for the price (stay in the same complex fields).
variable (F) in
def book (w n : ℕ) : (d : ℕ) → S.Field d → ℝ
  | 0, x => if w=0 then life F n x else 0
  | d+1, x=> if w≤d+1 then charge F n x+(dial n)⁻¹ * book w n d (floorAt F d n x) else 0
lemma positiveCharge (x:S.Field (d+1))(n:ℕ) : 0≤charge F n x := Real.sqrt_nonneg _
lemma positiveLife (x:S.Field d)(n:ℕ) : 0≤life F n x := Real.sqrt_nonneg _
lemma bookPos (F: Final C f S) (w n d) (x:S.Field d):0 ≤ book F w n d x:=by
   induction d with
   | zero=> by_cases he:w=0 <;> simp only [book,he,↓reduceIte]; exact Real.sqrt_nonneg _; exact le_rfl
   | succ d ih=> unfold book; split; exact add_nonneg (positiveCharge _ _) (mul_nonneg (inv_pos.mpr (dial_pos n)).le (ih _)); rfl
lemma bookAdd (F: Final C f S) (w n) (d:ℕ) (x y:S.Field d) :
   book F w n d (x+y) ≤ book F w n d x + book F w n d y :=by
   induction d with
   | zero=> by_cases he:w=0 <;> simp only [book,he,↓reduceIte,add_zero]; exact life_add F x y; rfl
   | succ d ih=>
     by_cases he:w≤d+1
     · simp only [book,if_pos he,charge,map_add]; exact (add_le_add (life_add F ..)
         (mul_le_mul_of_nonneg_left (ih ..) (inv_pos.mpr (dial_pos n)|>.le))).trans_eq (by ring)
     simp only [book,if_neg he,add_zero,le_refl]
lemma bookSub (F:Final C f S) (w n) (d:ℕ)(x y:S.Field d): book F w n d (x-y) ≤ book F w n d x+book F w n d y:= by
   have hn(d:ℕ)(x:S.Field d):book F w n d (-x)=book F w n d x:=by
     induction d with
     | zero=> simp [book,life,map_neg]
     | succ d ih=> simp only [book,charge,map_neg,life,_root_.neg_apply,neg_neg]; rw [ih]
   rw [sub_eq_add_neg]; exact (bookAdd F w n d x _).trans_eq (by rw [hn d y])
lemma dial_large (n) : 1 ≤ dial n := by simp [dial]
lemma budgeted (F:Final C f S) (w n) (d:ℕ) (h : ∀ e : ℕ,e ≤ d → Valid F e n) (x:S.Field d) :
   book F w n d x ≤ ((d:ℝ)+1) * life F n x:= by
   induction d with
   | zero=> simp only [book,Nat.cast_zero,zero_add,one_mul]; split; exact le_rfl; exact positiveLife x n
   | succ d ih=>
     have he :=h d (Nat.le_succ d)
     have hp:0≤ ((d:ℝ)+1):= by positivity
     unfold book; split
     · refine le_trans (add_le_add (cap_le F he x)
         ((mul_le_mul (inv_le_one_of_one_le₀ (dial_large n)) ((ih (fun i hi=>h i (by omega)) _).trans
           (mul_le_mul_of_nonneg_left (floor_le F he x) hp)) (bookPos ..) zero_le_one))) (le_of_eq ?_)
       push_cast; ring
     exact mul_nonneg (by positivity) (positiveLife x n)
lemma bookOrigin (F:Final C f S) (n d) (x:S.Field d) : life F n x ≤ (dial n)^d * book F 0 n d x:= by
   have hp :=dial_pos n
   induction d with
   | zero=> simp [book]
   | succ d ih=>
     let b:= floorAt F d n x; let t:= cap F d n x
     have hh: life F n x ≤ life F n b+charge F n x:= by
       have he: life F n x = life F n (liftA F d b+t):=congr_arg (life F n) (recombine F x)
       rw [he]; exact (life_add F ..).trans_eq (by rw [reflects_life]; rfl)
     rw [book,if_pos (Nat.zero_le _)]
     apply le_trans (hh.trans (add_le_add (ih b) (le_mul_of_one_le_left (positiveCharge (F:=F) x n) (one_le_pow₀ (n:=d+1) (dial_large n)))))
     rw [mul_add,add_comm, ← mul_assoc, show dial n^(d+1)*(dial n)⁻¹=dial n^d from by rw [pow_succ,mul_assoc,mul_inv_cancel₀ hp.ne',mul_one]]

-- numerical lemmas
lemma plusDial (n) : precision n = 1+(dial n)⁻¹ := by unfold precision; field_simp; simp
lemma baseDial (n) : 1 ≤ precision n := plusDial n ▸ (by linarith only [inv_pos.mpr (dial_pos n)])
lemma absorbs (C:ℝ) : ∃ v: ℕ, ∀ n:ℕ, 1 + C*(dial n)⁻¹ ≤ precision n^v := by
   obtain ⟨v,hv⟩:= exists_nat_ge C; refine ⟨v,fun n=>?_⟩; rw [plusDial]
   apply le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hv (inv_pos.mpr (dial_pos n)|>.le)))
   apply one_add_mul_le_pow
   linarith only [inv_pos.mpr (dial_pos n)]

-- offgrade price using monotone of OS for ANY vectors + orthogonal projections.
private lemma pricesShear (x:S.Field (d+1)) {n:ℕ}(h: Valid F d n) :
   life F n (floorAt F d n x - floorAt F d (n+1) x) ≤ charge F (n+1) x:= by
  have he: floorAt F d n x-floorAt F d (n+1) x=floorAt F d n (cap F d (n+1) x) :=by rw [Annulus.leaves,map_sub,retro F h]
  rw [he]; exact (floor_le F h _).trans (up F _ _ _)
lemma bookLower {n d w:ℕ}(x:S.Field d) (he:d<w): book F w n d x=0 := by
  cases d with
  | zero=> rw [book,if_neg (show w≠0 by omega)]
  | succ d=> rw [book,if_neg (by omega)]
lemma atSmall (B : Mantle F u)(d:ℕ):∀ᶠ n in atTop,∀ e, e ≤ d → Valid F e n:= by
  have ht(i:Fin (d+1)) : ∀ᶠ n in atTop,Valid F (i:ℕ) n:=by
    obtain ⟨r,hp,H⟩:=strictSmall F B i
    exact (plank_limit.eventually (ge_mem_nhds hp)).mono (fun n hn=> H _ (Real.exp_pos _) hn)
  filter_upwards [eventually_all.mpr ht] with n ht i hi; exact ht ⟨i,Nat.lt_succ_of_le hi⟩

-- per dyadic step bounds, with the proper weight D and inverse weight w. Includes
-- both constant K and all offgrade shear growth. This finishes the only needed induction on field d.
-- Note Fits is uniform in horizons separately.
variable (h : Fits F)(B:Mantle F u)
include B h
set_option maxHeartbeats 800000 in
lemma intermediates (d w:ℕ) (hw:w ≤ d) : ∃ i j:ℕ,
    ∀ᶠ n in atTop, ∀ x:S.Field d,
      book F w (n+1) d x ≤ epoch^d* precision n^i * book F w n d x ∧
      book F w n d x ≤ epoch⁻¹ ^ w * precision n^j * book F w (n+1) d x:= by
   have hE:= zero_lt_one.trans epoch_ge
   induction d with
   | zero=> obtain rfl := Nat.eq_zero_of_le_zero hw; obtain ⟨i,hi⟩:=h.vacuum; refine ⟨i,0,hi.mono fun n hn x=>?_⟩; simp [book]; exact ⟨hn x,up F ..⟩
   | succ d ih=>
     obtain ⟨t,ht⟩:=h.quota d
     rcases Nat.eq_or_lt_of_le hw with hW|hW
     · subst w; refine ⟨t,t,?_⟩; filter_upwards [ht] with n hn x; rw [book, if_pos le_rfl, book,if_pos le_rfl]; simp only [bookLower _ (Nat.lt_succ_self d),mul_zero,add_zero]; exact hn x
     have hW:w≤d:=Nat.le_of_lt_succ hW; obtain ⟨i,j,hA⟩:=ih hW
     let u:=dial d
     obtain ⟨s,hs⟩:= absorbs (epoch^d*u)
     obtain ⟨l,hl⟩:= absorbs (epoch^w*u)
     refine ⟨i+t+s,j+1+t+l,?_⟩; filter_upwards [ht, hA, atSmall B d] with n hn hi ha x
     let g:= floorAt F d n x; let g':= floorAt F d (n+1) x; let p:=precision n
     let a:= (dial n)⁻¹;let b:= (dial (n+1))⁻¹; let k:= epoch^(d+1);let y:= epoch⁻¹ ^w
     have hp : 1≤p := baseDial n
     have hb : 0 < b := inv_pos.mpr (dial_pos _)
     have hba : a=b*p := by unfold b p precision a; field_simp [(dial_pos n).ne',(dial_pos (n+1)).ne']
     have haq : b ≤ a:= hba ▸ le_mul_of_one_le_right hb.le hp
     have hs':= hb.trans_le haq
     let z:=charge F n x;let z':=charge F (n+1) x
     have hz :0 ≤ z:=positiveCharge _ _; have hZ : 0 ≤ z':= positiveCharge _ _
     have hz' : z' ≤ k*p^t*z:=(hn x).1
     have hpf : z ≤ y*p^t*z':= (hn x).2.trans (by gcongr; exact pow_le_pow_of_le_one (by positivity : 0≤epoch⁻¹) (inv_le_one_of_one_le₀ epoch_ge.le) hw)
     let D := book F w n d g; let D' := book F w (n+1) d g'
     have h' : book F w n d (g-g') ≤ u*z':=(budgeted _ _ _ d ha _).trans (mul_le_mul_of_nonneg_left
       (pricesShear x (ha d le_rfl)) (by positivity))
     have HD:0 ≤ D:=bookPos ..; have HD' : 0 ≤ D':=bookPos ..
     have hlow: D' ≤ epoch^d*p^i*(D + u*z'):= (hi g').1.trans (mul_le_mul_of_nonneg_left
       (by nth_rw 1 [show g'=g-(g-g') by abel]; exact (bookSub F w n d g _).trans (add_le_add le_rfl h')) (by positivity))
     have hhigh: D ≤ y*p^j * D' + u*z' := by
        apply le_trans (b:=book F w n d g' + book F w n d (g-g'))
        · unfold D; nth_rw 1 [show g=g'+(g-g') by abel]; exact bookAdd F w n d g' _
        exact add_le_add (hi g'|>.2) h'
     rw [book, if_pos hw, book,if_pos hw]
     constructor
     · change z'+b*D' ≤ k*p^(i+t+s)*(z+a*D)
       have hb' : b*(epoch^d*p^i*D) ≤ k*p^(i+t+s)*(a*D):=calc
          _ ≤ a*(k*p^(i+t+s)*D) := mul_le_mul haq (by unfold k;gcongr <;> first | exact epoch_ge.le | exact hp | omega) (by positivity) hs'.le
          _ = _ := by ring
       calc
         _ ≤ z' + b*(epoch^d*p^i*(D+u*z')) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlow hb.le)
         _ = (1+epoch^d*u*b*p^i)*z' + b*(epoch^d*p^i*D) := by ring
         _ ≤ p^(i+s)*(k*p^t*z) + k*p^(i+t+s)*(a*D) := add_le_add (mul_le_mul (show 1+epoch^d*u*b*p^i ≤ p^(i+s) from calc
                  _ ≤ p^i+epoch^d*u*a*p^i:=by gcongr; exact one_le_pow₀ hp
                  _ = p^i*(1+epoch^d*u*a):=by ring
                  _ ≤ p^(i+s):=by rw [pow_add]; exact mul_le_mul_of_nonneg_left (hs n) (by positivity)) hz' hZ (by positivity)) hb'
         _ = _ := by simp only [pow_add]; ring
     have hy:(0:ℝ)≤y:=by unfold y; positivity
     change z+a*D ≤ y * p^(j+1+t+l) * (z' + b * D')
     calc
       _ ≤ y*p^t*z'+a*(y*p^j*D'+u*z'):=add_le_add hpf (mul_le_mul_of_nonneg_left hhigh hs'.le)
       _ = y*(p^t+(epoch)^w*u*a)*z'+y*p^(j+1)*(b*D'):=by unfold y; rw [inv_pow,hba]; field_simp; ring
       _ ≤ _:= by
            rw [mul_add (y*p^(j+1+t+l))]; apply add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hy) hZ)  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega : j+1 ≤ j+1+t+l)) hy) (mul_nonneg hb.le HD'))
            let C:=epoch^w*u*a; have hC:0≤C:=by unfold C u; have := dial_pos d; positivity
            calc
              _ ≤ p^t*(1+C) := by rw [mul_add (p^t),mul_one]; exact add_le_add le_rfl (le_mul_of_one_le_left hC (one_le_pow₀ hp))
              _ ≤ p^(t+l):= by rw [pow_add]; exact mul_le_mul_of_nonneg_left (hl n) (by positivity)
              _ ≤ _:= pow_le_pow_right₀ hp (by omega)

end YM.SharpGram.Annulus
