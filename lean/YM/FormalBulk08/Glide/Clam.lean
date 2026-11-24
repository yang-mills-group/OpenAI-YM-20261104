import YM.FormalBulk08.Glide.Spree

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{m r:ℕ}{L : Side}{I J : Type}
lemma telescope_bail {V E: Type*}(W:Reach V) (F : (Fin r→ E) → Tile V m)(admissible:E →Prop)(U S:E)(hu:admissible U)(hs:admissible S)(h : ∀ Z,(∀ i,admissible (Z i)) → ∀ i,Bail W σ (F (update Z i U)-F (update Z i S)) B)(_hb:0≤B) : Bail W σ (F (fun _=>U)-F (fun _=>S)) (r*B):= by
   let P (T:Finset (Fin r))(i:Fin r):= if i∈T then U else S
   have hh (T:Finset (Fin r)):Bail W σ (F (P T)-F (fun _=>S)) (T.card*B):= by
       induction T using Finset.induction with
       | empty=> rw [show P ∅=fun _=> S from funext fun _=>by simp [P], sub_self]; simpa only [Finset.card_empty,Nat.cast_zero,zero_mul] using bail_void ..
       | @insert i K hi ih=>
         have hp: update (P K) i U= P (insert i K) := by ext t;by_cases h:t=i <;> simp [P,h]
         have hx: update (P K) i S=P K:= by
            conv_lhs => arg 3; rw [show S=P K i from (if_neg hi).symm]
            exact update_eq_self ..
         have ht:= (h (P K) (fun j=> by unfold P;split; exacts [hu,hs]) i).add ih
         rw [hp,hx, sub_add_sub_cancel] at ht; rw [Finset.card_insert_of_notMem hi, Nat.cast_add_one,add_mul,one_mul, add_comm]; exact ht
   simpa [P] using hh Finset.univ
variable [Fintype I]
lemma boat {S S' : Cross L (colorsL G) I}{U:Cross L (spots G) I}{T:Tile (edgeL G) (m+1)}(h:trench (minusRows S S') U)(p:0≤σ)(q:0≤η)(he:η ≤ L.val * σ)(hp:Bail (fame _) σ T B)(hq:Bail (fame _) σ (tap T) D)(hw:S.strip η C)(hS:S'.strip η C)(ha:U.strip η C)(hc:0≤C)(ht:Agate T):
   Bail (fame _) η (pearl (merit S) T-pearl (merit S') T) ((m+1)* (Real.exp (8*η)*D*(Fintype.card (Co L (colorsL G))*(Fintype.card I:ℝ)^m)*(C+C)^(m+1))) := by
    let F (Z:Fin (m+1)→Cross L (colorsL G) I):=prism (fun i:Fin (m+1)=>merit (Z i)) T
    have hh (Z:Fin (m+1)→Cross L (colorsL G) I)(hz:∀ i,(Z i).strip η C)(i:Fin (m+1)):
        Bail (fame _) η (F (update Z i S)-F (update Z i S')) (Real.exp (8*η)*D*(Fintype.card (Co L (colorsL G))*(Fintype.card I:ℝ)^m)*(C+C)^(m+1)) := by
       let K:= jetty (Bank.scroll L (colorsL G)).symm T
       have hy:=Bank.packet_bill L he q hp
       have HB: C≤ C+C:= le_add_of_nonneg_left hc
       have heq (t:Fin (m+1)→Cross L (colorsL G) I): F t=prism (fun i=> lands (t i)) K:=tower _ _ rfl t
       rw [heq,heq,twin_arcs q hc K hy i hw hS Z hz,← heq]; exact prism_tap h p q hp hq (strip_minus hw hS) (strip_mono ha le_rfl HB) (hc.trans HB) Z (fun i=>strip_mono (hz i) le_rfl HB) ht i he
    have hd:=hq.1; have ht:= telescope_bail _ F (fun V=>Row.strip V η C) S S' hw hS hh (by positivity)
    push_cast at ht; exact ht

end YM.FormalBulk08.Glide
