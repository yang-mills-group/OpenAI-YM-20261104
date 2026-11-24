import YM.Contacts.Harrier.Spokes
import YM.Contacts.Procession.Bowling
import YM.Contacts.Procession.Conduit
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Cartons PowerSeries
-- acting on coefficients in their own LOCAL variable
abbrev RodP:= PowerSeries ℝ
def surge (P:Sketch G)(n:ℕ): Sketch G:=fun p=> shiftA n (P p)
def fresh (w:RodP)(V:Sketch G)(k:ℕ): Sketch G:=∑ i∈Finset.range (k+1), pin w i • surge V i
def whip (w:RodP)(V:Sketch G): Sketch G:= fun s i=> fresh w V i s i
variable {x:Dye G}{V P:Sketch G} {d':ℕ}(H:Labels.Frame G d')
lemma fresh_same (w:RodP)(V:Sketch G)(h:i≤j)(s:Cards): whip w V s i=fresh w V j s i:= by
   unfold whip fresh; simp_rw [Finset.sum_apply]; refine sum_subset (Finset.range_mono (by omega)) (fun b _ hb=>?_); change pin w b • (surge V b s i)=0; have he:b>i:= by simp only [Finset.mem_range] at hb; omega
   rw [surge,shiftA,if_neg (by omega),smul_zero]
namespace Living
variable (hu:Living x M D V ζ)
include hu
lemma surgeM (n:ℕ):Living x M D (surge V n) ζ:= by
   refine ⟨⟨fun f g=>?_,fun f g=>?_⟩,fun v=> (hu.lineage v).shift _,fun i j=>?_ ⟩; · unfold surge; rw [hu.lin.map_add]; exact shift_add ..
   · unfold surge; rw [hu.lin.map_smul]; exact shift_scale ..
   unfold sail surge shiftA; split_ifs; exact hu.budget ..; exact ⟨_,le_refl 0,w_zero⟩
lemma whipM (w: RodP): Living x M D (whip w V) ζ:= Living.closed fun i=> ⟨fresh w V i, Living.sum _ (fun j _=> (hu.surgeM j).scale _), fun s _ h=> fresh_same w V h s⟩
end Living
-- projection fill (addresses applied outside the slot). coefficient and rank.E support. Use at H≥slot cap as needed
variable {Y Z: bore G}
private lemma pitch_empty (X:bore G) (h:Mount X M)(U:TableFee)(t: Price X x ζ U)(hζ:0<ζ) (l:ℕ)(f:H.Index)(h0:∀ v≤ (H.grades f).2,coil X M l v=0):velum H (coil X M l) f=0:= vela_silent (coil_tags h t hζ _) _ h0 -- args
lemma fill_null (x:Dye G)(u:H.Index)(k M:ℕ):fill H M 0 k u=0:= by
   obtain ⟨hp,V,hV⟩:= (Based.zero (M:=M) (ζ:=1) (v:=x)); unfold fill; split; · apply pitch_empty H 0 hp V hV zero_lt_one _ u; intro v hv; unfold coil dazzle shiftA; split_ifs <;> rfl
   rfl
lemma coil_linear (Y Z:bore G)(a:ℝ): coil (a • Y + Z) M l= a • coil Y M l + coil Z M l:= by ext1 i; simp only [coil,dazzle,Pi.smul_apply,Pi.add_apply,shift_add,shift_scale]; split_ifs <;> simp
lemma fill_linear (hp:Based ζ x M Y)(he:Based ζ x M Z)(hζ:0<ζ) (a:ℝ)(l:ℕ)(f:H.Index): fill H M (a • Y+Z) l f=a*fill H M Y l f+ fill H M Z l f:= by
   have ht:=(hp.smul a).add he; obtain ⟨hp,W,hW⟩:=hp; obtain ⟨he,T,hT⟩:=he; obtain ⟨hx,U,hU⟩:=ht; unfold fill; split; · rename_i hl; have hv (n:ℕ):= coil_tags hx hU hζ n; simp_rw [coil_linear] at hv; rw [coil_linear]; exact peek_linear (coil_tags hp hW hζ _) (coil_tags he hT hζ _) _ (hv _) _
   simp
private lemma ascend (Y : House X) (M j:ℕ)(h:j ≤ i) : coil (shiftA j Y) M i = coil Y M (i-j):= by
   ext1 r; unfold coil dazzle shiftA; split_ifs <;> first | rfl| omega | (apply congr_arg (· r) ∘ congr_arg Y; omega)
lemma fill_shift (h:Based ζ x M Y)(hζ:0<ζ)(f:H.Index)(b i:ℕ): fill H M (shiftA b Y) i f=if b ≤ i then fill H M Y (i-b) f else 0:= by
   let k:=(H.grades f).2; let l:=M+4+i-k
   obtain ⟨he,V,hV⟩:= h.shift b; obtain ⟨h,U,hU⟩:=h; by_cases hp:b ≤ i
   · rw [if_pos hp]; unfold fill; split; swap; · rw [if_neg (by omega)]
     next hk=>
       split; · rw [ascend Y M b (by omega)]; apply congr_arg (fun i=> velum H (coil Y M i) f); omega -- b ≤ l? might if l small? r<= M+i ignores b. second condition k ≤M+i-b
       next ht=>
         apply vela_silent (coil_tags he hV hζ _) _; intro v hv; unfold coil dazzle shiftA; split; split; split; apply h.incarnate.thin; unfold Catch.cap at *; omega; rfl; rfl; rfl
   · rw [if_neg hp]; unfold fill; split; · apply vela_silent (coil_tags he hV hζ _) _; intro v hv; unfold coil dazzle shiftA; split_ifs <;> first| rfl| (unfold Catch.cap at *; omega) -- impossible
     rfl
lemma fill_thin (u:H.Index)(hq:(H.grades u).2> M+k) (V:bore G): fill H M V k u=0:= if_neg (by omega)
lemma fill_lag (h:Based ζ x M Y)(hp:Based ζ x M Z)(hx:0<ζ)(f:H.Index)(he:∀ j ≤ i,Y j=Z j): fill H M Y i f=fill H M Z i f:= by
    unfold fill; split; swap; · rfl
    next hh =>
     let p:ℝ:= -1; let V:=p • Z+Y; obtain ⟨hv,T,hw⟩:= (hp.smul p).add h; let k:=(H.grades f).2; let l:=M+4+i-k; have hf: velum H (coil V M l) f=0:= by
        apply vela_silent (coil_tags hv hw hx _) _; intro j h'; unfold coil dazzle shiftA; split_ifs <;> first | rfl | simp [he (l+j-2-Catch.cap M) (by unfold l Catch.cap k; omega),p]
     unfold V p at hf
     have he' := fill_linear H hp h hx (-1) i f; simp only [fill,if_pos hh] at he'; linarith only [hf, he']
lemma fill_ignite (h:Living x M D V ζ)(hx:0<ζ)(w:RodP)(f:H.Index)(u:Cards)(i:ℕ): fill H M (whip w V u) i f= ∑ j∈Finset.range (i+1), pin w j * fill H M (V u) (i-j) f:= by
    let S:= Finset.range (i+1); let y j:=pin w j • surge V j
    have hY j: Living x M D (y j) ζ:= (h.surgeM j).scale _
    rw [fill_lag H ((h.whipM w).lineage _) ((Living.sum S (fun i _=> hY i)).lineage u) hx f (fun i h=>fresh_same w V h u)] -- proof use directions
    calc
      _= ∑ j∈S, fill H M (y j u) i f := ?_
      _= _:= Finset.sum_congr rfl fun j hj=> by have he:=fill_linear H ((h.surgeM j).lineage u) (Based.zero (v:=x) (M:=M) (ζ:=ζ)) hx (pin w j) i f; change fill H M _ i f=_; erw [show y j u= _ from (show _=pin w j • (surge V j u)+0 from (add_zero _).symm),he,fill_null H x]; unfold surge; rw [fill_shift H (h.lineage u) hx,if_pos (show j ≤ i from by simp [S] at hj;omega),add_zero]
    let K:= fun F: ↥(Area x M D ζ)=> fill H M (F.val u) i f; -- workaround sum.Add/Pi.
    suffices h : ∀ S:Finset ℕ,fill H M ((∑ j∈S,y j) u) i f=∑ j∈S,fill H M (y j u) i f by exact h _
    intro s; induction s using Finset.induction with
    | empty => simp only [Finset.sum_empty,Pi.zero_apply]; apply fill_null H x
    | insert j v hj ih=>
       let p:= V; simp only [sum_insert hj,Pi.add_apply]; apply (show _=fill H M (y j u) i f+fill H M ((∑ j∈v,y j) u) i f from (by simpa only [one_smul,one_mul] using fill_linear H ((hY j).lineage u) ((Living.sum v fun w _=>hY w).lineage u) hx 1 i f)).trans (congr_arg (fill H M (y j u) i f+·) ih)
end
end YM.Contacts.Harrier
