import YM.WilsonCoeffUV.Reclosure.Technical
import YM.WilsonCoeffUV.Reclosure.Paths.SignedPackets
/-!
# Common representative of ALL finer comparisons at a fixed finite inspected horizon

Overlay infinite reference on the same walks, rather than assert a bounded
operation changing representative after evaluation with lost origins.
`Layered` keeps alignment data (actual paths & weights); fees are on this
representation. No claim it transports a general chosen E/Bianchi gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{k r t e m:ℕ}{s A B a:ℝ}{P Q T: Stack G r}

def plus_at (P Q: Stack G r): Stack G r:= fun j=>{leg:= (P j).leg, coeff:= (P j).coeff+(Q j).coeff}
lemma overlay_s (X Y:Atom G r)(U: Atom G r)(p:U.coeff=X.coeff+Y.coeff) (x): U.poly x=X.poly x+Y.poly x:=by unfold Atom.poly; simp [p,add_mul,Finset.sum_add_distrib]
private lemma cap_add {f g:ℕ→ℝ}(p:SumBudget f A)(q:SumBudget g B): SumBudget (fun i=>f i+g i) (A+B):= ⟨fun i=>add_nonneg (p.1 i) (q.1 i),p.2.1.add q.2.1,(p.2.1.tsum_add q.2.1).trans_le (add_le_add p.2.2 q.2.2)⟩
lemma canvas_paid (p:Deed P)(q:Deed Q)(h:Commission P s A e)(g:Commission Q s B e): Commission (plus_at P Q) s (A+B) e:=by
    let T:= plus_at P Q
    have hx i: (P i).leg=(Q i).leg:= (p i).trans (q i).symm
    constructor
    · intro i v x; rw [overlay_s (P i) (Q i) (T i) rfl, overlay_s (P i) (Q i) (T i) rfl (show Fin _ →G.Color from x),h.hue i v,g.hue i v]
    · apply budget_minor (cap_add h.toll g.toll) (fun i=> fiscal T i s) _
      intro i
      have ht :(T i).magnitude≤ (P i).magnitude+(Q i).magnitude:= by
        unfold Atom.magnitude; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro j _; exact abs_add_le ..
      have hr: (P i).length=(Q i).length:= by unfold Atom.length; rw [hx i]
      change (T i).magnitude*Real.exp (s*(P i).length)≤_
      apply (mul_le_mul_of_nonneg_right ht (by positivity)).trans_eq
      unfold Atom.budget; rw [add_mul,hr]
    intro he; have hu:=h.loan he; have hh:= g.loan he; cases r with
    | succ r=> trivial
    | zero=>
      change Sprite P at hu; change Sprite Q at hh; change Sprite (plus_at P Q)
      intro i x
      have hv : silentPay (plus_at P Q) i x=silentPay P i x+silentPay Q i x:= by funext k; unfold silentPay plus_at; simp only [hx,Pi.add_apply]; split<;> simp
      constructor
      · rw [hv]; exact add_zero (0:ℝ) ▸ ((hu i x).1.add (hh i x).1)
      intro l; rw [show (fun k=>forceCoin (plus_at P Q) i x k l)= (fun k=>forceCoin P i x k l)+(fun k=>forceCoin Q i x k l) from ?_]
      · exact add_zero (0:ℝ) ▸ (((hu i x).2 l).add ((hh i x).2 l))
      funext k; unfold forceCoin; rw [hv]; simp only [plus_at,Pi.add_apply,hx,add_mul]

lemma plus_score (hv:0<s)(p:Deed P)(q:Deed Q) (h:Commission P s A e)(g:Commission Q s B e)(n:Side):
    seriesScore n (plus_at P Q)= seriesScore n P+seriesScore n Q:=by
    let C (x:Stationary.Link G n) := input G n x
    have hy (R : Stack G r) (E:ℝ) (t: Commission R s E e) (x:Link G n)(p:Site n): Summable (fun i=>(R i).unmasked (C x) p):= by
       apply Summable.of_norm_bounded (t.toll.2.1.mul_right (2^(r+2))) (fun i=>?_); exact ((R i).unmasked_bound _ _).trans (mul_le_mul_of_nonneg_right ((R i).lower_budget s hv) (by positivity))
    funext x; unfold seriesScore Precision.uncut; rw [Pi.add_apply, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; change _=(∑' k,(P k).unmasked (C x) i)+(∑' k,(Q k).unmasked (C x) i)
    rw [← (hy P A h x i).tsum_add (hy Q B g x i)]; apply tsum_congr; intro j
    rw [Atom.unmasked,overlay_s (P j) (Q j) (plus_at P Q j) rfl];
    let T : Fin (r+2) → G.Color:= fun v=> ((P j).leg v).atSite (C x) i
    change _+(Q j).poly T=_+ (Q j).unmasked _ _
    have hz: T=(fun v=> ((Q j).leg v).atSite (C x) i):=by unfold T; rw [p j,q j]
    exact congr_arg ((P j).unmasked (C x) i+·) (congr_arg ((Q j).poly) hz)
lemma fire_merge (hv:0<s)(p:Deed P)(q:Deed Q)(h:Commission P s A e)(g:Commission Q s B e)(k):
    fire (plus_at P Q) k= fire P k + fire Q k:=by
   ext1 r; apply (paid_packet hv (canvas_paid p q h g).toll (by omega) k r).unique
   refine ((paid_packet hv h.toll (by omega) k r).add (paid_packet hv g.toll (by omega) k r)).congr (Eventually.of_forall (fun n=>?_))
   change (written P n k r+written Q n k r)=written (plus_at P Q) n k r
   unfold written; rw [plus_score hv p q h g]
   unfold sprig; rw [rye_plus _ _ (score_analytic n _ hv h.toll).contDiffAt (score_analytic n _ hv g.toll).contDiffAt]
   -- shine light manually
   rename_i t; by_cases H:t+2+k=r; subst r; simp only [shine_lit]
   simp only [shine_dark H,zero_add]

-- typed assignment per layer: prices absolute W committed.
inductive Layered (G:Gauge): SeriesA G → SeriesA G → SeriesA G → Prop where
   | empty: Layered G [] [] []
   | glued {m r:ℕ}(P Q:Stack G r) {X Y Z:SeriesA G} (h:r≤m)(p:Deed P)(q:Deed Q)(u:Layered G X Y Z): Layered G (⟨m,r,h,P⟩::X) (⟨m,r,h,Q⟩::Y) (⟨m,r,h,plus_at P Q⟩::Z)
lemma tracts {X Y Z: SeriesA G}(h:Layered G X Y Z): Z.length=X.length ∧ desk Z=desk X ∧ seals Z:=by
   induction h with
   | empty=> exact ⟨rfl,rfl,by simp [seals]⟩
   | glued P Q h p q _ ih=> exact ⟨by simp [ih.1],congr_arg₂ List.cons rfl ih.2.1 /-  ⟨rfl,ih.2.1⟩ -/,fun i hi=> (List.mem_cons.mp hi).elim (fun e=> e.symm ▸ (show Deed (plus_at P Q) from fun i=>p i)) (ih.2.2 i)⟩
lemma estates {X Y Z:SeriesA G}(h:Layered G X Y Z)(hv:0<s)(hp:Draw X s A)(hq:Draw Y s B): murals Z=murals X+murals Y ∧ Draw Z s (A+B):=by
   induction h with
   | empty=> exact ⟨by simp [murals],draw_nil (add_nonneg hp.1 hq.1)⟩
   | @glued m r P Q X Y Z h p q u ih=>
      let aP:PrismA G:= ⟨m,r,h,P⟩; let aQ:PrismA G:=⟨m,r,h,Q⟩; let b:PrismA G:= ⟨m,r,h,plus_at P Q⟩
      obtain ⟨H,W⟩:=ih ⟨hp.1,fun _ x=>hp.2 _ (List.mem_cons_of_mem _ x)⟩ ⟨hq.1,fun _ x=> hq.2 _ (List.mem_cons_of_mem _ x)⟩
      have hx:=hp.2 aP (List.mem_cons_self ..); have hz:=hq.2 aQ (List.mem_cons_self ..)
      have he : recordV b = recordV aP+ recordV aQ:= by funext i; simp only [recordV,chess, b,aP,aQ,Pi.add_apply]; split; exact fire_merge hv p q hx hz _; simp
      refine ⟨by simp_rw [murals_cons,H]; change recordV b+_=recordV aP+_+(recordV aQ+_); rw [he]; abel, W.1,fun i hi=>(List.mem_cons.mp hi).elim (fun h=>h.symm ▸ canvas_paid p q hx hz) (W.2 i)⟩
lemma actors {X Y:SeriesA G}(p: desk X=desk Y)(g:seals X)(h:seals Y): ∃ Z,Layered G X Y Z:=by
    induction X generalizing Y with
    | nil=> have he:Y=[]:= by simpa [desk] using p.symm
            subst Y; exact ⟨[],.empty⟩
    | cons i X ih=> cases Y with
                    | nil=> simp [desk] at p
                    | cons j Y =>
                       obtain ⟨m,r,b,P⟩:= i; obtain ⟨k,t,d,Q⟩:= j; simp only [desk,List.map_cons,List.cons.injEq,Prod.mk.injEq] at p
                       obtain ⟨⟨rfl,rfl⟩,e⟩:=p
                       obtain ⟨Z,v⟩:=ih e (fun _ x=>g _ (List.mem_cons_of_mem _ x)) (fun _ x=>h _ (List.mem_cons_of_mem _ x))
                       exact ⟨_,.glued _ _ b (g _ (List.mem_cons_self ..)) (h _ (List.mem_cons_self ..)) v⟩
lemma built {X:SeriesA G}(p:fromBefore X e)(Y:SeriesA G)(h:desk Y=desk X): fromBefore Y e:=by
    intro i hi; have ht:(i.grade,i.rise)∈desk Y:= List.mem_map.mpr ⟨i,hi,rfl⟩; rw [h] at ht
    obtain ⟨j,hj,e⟩:= List.mem_map.mp ht
    exact (Prod.mk.inj e).1 ▸ p j hj

variable {U W:Credit}
-- same displays output series only at declared finite order. signs expose entire representatives for corresponding channels.
def signed_eval (P:SeriesA G) : Canvas G:= fun e r=> huesT (murals P e r)
theorem plated (G:Gauge)(e:ℕ)(T U:Credit):∃ V:Credit,∀ R:Realm G e T,Inkplate e R U→∀ m (h:R.anchor≤m), ∃ Y:SeriesA G, DisplayA G Y (peak R m h) (R.cash V m) e (timeless R.draws R.paid m) ∧
    (∀ i ≤ e,signed_eval Y i = timeless R.draws R.paid m i ∧ ∀ n:Side,∀ r,sands Y n i (r+1)=lagoon (timeless R.draws R.paid m i (r+1)) n) ∧
    ∀ N≥m, ∃ Z F: SeriesA G, DisplayA G Z (peak R m h) (R.cash V m*R.tempC m N) e (actionW R.draws R.paid N m-timeless R.draws R.paid m) ∧ Layered G Y Z F ∧
        DisplayA G F (peak R m h) (R.cash V m+R.cash V m*R.tempC m N) e (actionW R.draws R.paid N m) ∧
        ∀ i≤ e,signed_eval F i=actionW R.draws R.paid N m i ∧ ∀ n:Side,∀ r,sands F n i (r+1)= lagoon (actionW R.draws R.paid N m i (r+1)) n:=by
    obtain ⟨V,hV⟩:= covenants G e T U
    refine ⟨V,fun R t m h=>?_⟩; obtain ⟨P,y,v⟩:= hV R t m h
    let I:= peak R m h; have hg:0<I:=ret_pos G (e+1) (R.mint m h).σ (R.mint m h).width
    have hx (X F K) (x:DisplayA G X I K e F) (p:∀ i≤ e,∀ r s z,F i r (tickW s 0 ∘ z)= veil z s* F i r z): ∀ i ≤ e,signed_eval X i= F i ∧∀ n:Side,∀ r,sands X n i (r+1)=lagoon (F i (r+1)) n:=by
       intro i z; have he: signed_eval X i=F i:= funext (fun r=>by unfold signed_eval; rw [x.sewn i (by omega)]; exact huesT_same (p i z r))
       exact ⟨he,fun n r=> (wraps_signed hg X x.charge i r n).trans (congr_arg (fun f:post G r=> lagoon f n) (congr_fun he (r+1)))⟩
    refine ⟨P,y,hx P _ _ y (fun i j k s x=> (modern R h).s i j k s 0 x),?_⟩
    intro N hn; obtain ⟨X,x,w⟩:=v N hn; obtain ⟨F,f⟩:=actors (y.census.trans x.census.symm) y.reads x.reads
    have hy:= estates f hg y.charge x.charge
    obtain ⟨ht,H,u⟩:=tracts f
    have p: DisplayA G F I (R.cash V m+R.cash V m*R.tempC m N) e (actionW R.draws R.paid N m):=⟨fun i hi=> by rw [hy.1,← murals_append]; exact w i hi,built y.placed F H, hy.2,ht.trans y.length,H.trans y.census,u⟩
    exact ⟨X,F,x,f,p,hx _ _ _ p (fun i _ j s x=> (catchment R.draws R.paid R.hG R.green hn).signs s 0 i j x)⟩
end YM.WilsonCoeffUV.Bank.Mosaic
