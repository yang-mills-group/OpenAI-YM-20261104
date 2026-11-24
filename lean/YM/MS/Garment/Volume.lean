import YM.MS.Garment.Rhyme
/-!
# Apparel, Book rank mask and sweeping premises

Orders at mixed n-sector m radius, ghost int packaging. No free cutoff cost until chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
open Color Book
variable {G:Gauge}{b c:Bool}{m n:ℕ}{s:ℝ}{F H: Mob G}{U:Rip G}{i j k:ℤ}{t:ℂ}
-- Pol mass rank ops

def Goods (k:ℤ)(F:Mob G): Prop:=∀ m, Book.rank k (F m)
abbrev Issue (k:ℤ)(F:Mob G): Prop:=∀ m, Limit (F m) k

def spot (t:ℤ): Signal.MH (Mob G) where
   toFun F m:= Book.mask t (F m)
   map_smul' c F:= funext fun m=> map_smul (Book.mask t) c (F m)
   map_add' F H:= funext fun m=> map_add (Book.mask t) (F m) (H m)
lemma goods_sp (F:Mob G)(k:ℤ): Goods k (spot k F):= fun m=> Book.rankMod ( F m) k
lemma spotted {l:Legs (Shore G m)}(h:(l.length:ℤ)=i) : spot i F m l= F m l:= Book.enough _ h
lemma spotsOff {l:Legs (Shore G m)}(h:(l.length:ℤ)≠i) : spot i F m l=0:= Book.strange _ h
structure Collar (i:ℤ)(F:Mob G): Prop where
    sym : Rock.sym F
    color : ShadeG F
    ghost : Ghost i F
lemma ranks_off {i:ℤ}(H:Goods i F)(l:Legs (Shore G n))(hp:(l.length:ℤ)≠i): F n l=0 := H n l ((mod_int l) ▸ hp) -- wrong direction?
lemma spotsP (h:Goods i F): spot i F= F:= funext (fun n=> rank_hat i |>.mp (h n)) -- reorder
lemma beam_mask (p:Pilot ℂ (SectorP m) (Landau.parity (A:=L m) (C:=G.ColorIndex)))(F:Rack G m)(k:ℤ): beam p (Book.mask k F)=Book.mask k (beam p F):= by
    ext l; induction l generalizing F k with| nil=> simp [Book.mask]| cons a l ih=> simp only [D_eval a, Book.conn, served, Finset.sum_apply,Pi.smul_apply, ih,map_sum,map_smul]
lemma Spot_g {k:ℤ} (h:Sturdy b F): Sturdy b (spot k F) where
    turn n g hg:= by change beam _ (Book.mask _ _)=_; rw [beam_mask,h.turn n _ hg]; rfl
    grows h' i:= by change Book.mask _ _ _=_; by_cases hp:(i.length:ℤ)=k; rw [Book.enough _ (by simp [Arts.lift,hp]), h.grows h',spotted hp]; rw [strange _ (by simpa [Arts.lift] using hp), spotsOff hp]
lemma spot_spec (k:ℤ)(h:Collar i F): Collar i (spot k F) where
    sym n l p q r:= by by_cases hx:((l++p::q::r).length:ℤ)=k; rw [spotted hx,spotted (by simpa using hx)]; exact h.sym .. ; rw [spotsOff hx,spotsOff (by simpa using hx),mul_zero]
    ghost n l hl:= by by_cases he:(l.length:ℤ)=k; exact (spotted he).trans (h.ghost _ _ hl); exact spotsOff he
    color n g:= by rw [← brush]; change beam _ (Book.mask _ _) = _; rw [beam_mask,brush g,h.color n g]; rfl
lemma spot_F (v:ℤ)(h:Sight F): Sight (spot v F):= by intro n l; by_cases he:(l.length:ℤ)=v; rw [spotted (by simpa [invertMom] using he),spotted he,h]; rw [spotsOff (by simpa [invertMom] using he),spotsOff he,star_zero]
lemma spot_fall {I:Type}{a:I→ℝ}{z:Arc.UScale I}{F:I→ Mob G}(h:fell z a F)(v:ℤ): fell z a (fun i=>spot v (F i)):= by
   intro n E _ _ _ w; by_cases he:(w.length:ℤ)=v; · unfold fieldVal; simp_rw [show ∀ (x) (i),spot v (F i) n (sail w x)=F i n (sail w x) from fun x i=>spotted (by simpa using he)]; exact h n E w
   unfold fieldVal; simp_rw [show ∀ x i,spot v (F i) n (sail w x)=0 from fun x i=> spotsOff (by simpa using he)]; exact Costs.zero (fun i _ _=> znon h i)
lemma spotM (k:ℤ)(h:Form0 b F): Form0 b (spot k F):=⟨ spot_fall h.price k, Spot_g h.token⟩
lemma spot_hol {D:Set ℂ}{F:ℂ→ Mob G}(he:Hol D F)(m:ℤ): Hol D fun i=>spot m (F i):= by
    refine ⟨fun c R hq hP=> spot_fall (he.price c R hq hP) m,fun n l=>?_⟩; by_cases h:(l.length:ℤ)=m; · simp_rw [spotted h]; exact he.top _ _
    simp_rw [spotsOff h]; exact fun i hi=> differentiableAt_const _
end YM.MS.Garment
