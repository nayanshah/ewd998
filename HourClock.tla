---- MODULE HourClock ----
EXTENDS Integers

VARIABLE Hour, AmPm
vars == <<Hour, AmPm>>

Init ==
    /\ Hour \in 1..12
    /\ AmPm \in { "AM", "PM" }

Next ==
    /\  IF Hour = 12
        THEN Hour' = 1
        ELSE Hour' = Hour + 1
    /\  IF Hour = 11
        THEN IF AmPm = "AM"
            THEN AmPm' = "PM"
            ELSE AmPm' = "AM"
        ELSE UNCHANGED AmPm

IsValid == Hour \in 1.. 12

CheckState ==
    /\ [][/\ Hour = 11 /\ AmPm = "AM" => Hour' = 12 /\ AmPm' = "PM"]_vars
    /\ [][/\ Hour = 11 /\ AmPm = "PM" => Hour' = 12 /\ AmPm' = "AM"]_vars

====