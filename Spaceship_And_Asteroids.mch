/* Spaceship_And_Asteroids
* Author: Arnold Anthonypillai
* Creation date: 06/11/2018
*/
MACHINE
    Spaceship_And_Asteroids
    
SETS
    NAVIGATION = 
    { 
        moveUp, 
        moveDown, 
        moveForward, 
        moveBackward 
    } ;
    
    STATUS = 
    { 
        Game_WON,
        Game_LOST,
        Game_Not_Over
    } ;
    
    REPORT = 
    { 
        MOVE_UP_SUCCESS, 
        MOVE_DOWN_SUCCESS,
        MOVE_FORWARD_SUCCESS,
        MOVE_BACKWARD_SUCCESS,
        CANNOT_MOVE__OUT_OF_SPACE_BOUNDARY, 
        CANNOT_MOVE__REGION_OCCUPIED_BY_AN_ASTEROID, 
        CANNOT_MOVE__NOT_ENOUGH_POWER_AVAILABLE,
        SPACESHIP_DOCKED,
        SPACESHIP_NOT_DOCKED,
        WARP_DRIVE_SUCCESS,
        CANNOT_ENGAGE_WARP_DRIVE__REGION_OCCUPIED_BY_AN_ASTEROID,
        CANNOT_ENGAGE_WARP_DRIVE__NOT_ENOUGH_POWER_AVAILABLE
    } 
    
CONSTANTS
    grid, 
    grid_x_axis, 
    grid_y_axis, 
    grid_x_axis_begin, 
    grid_x_axis_end, 
    grid_y_axis_begin, 
    grid_y_axis_end,
    homebase, 
    starbase,
    asteroidsPos,
    navPower,
    warpDrivePower,
    asteroidCrashedPower
    
PROPERTIES
    grid_x_axis <: NAT1 & grid_x_axis = 1..12
    &
    grid_y_axis <: NAT1 & grid_y_axis = 1..7
    &
    grid : NAT1 <-> NAT1 & grid = grid_x_axis * grid_y_axis 
    &
    grid_x_axis_begin : NAT1 <-> NAT1 & grid_x_axis_begin = { 1 } <| grid 
    &
    grid_x_axis_end : NAT1 <-> NAT1 & grid_x_axis_end = { 12 } <| grid 
    &
    grid_y_axis_begin : NAT1 <-> NAT1 & grid_y_axis_begin = grid |> { 1 } 
    &
    grid_y_axis_end : NAT1 <-> NAT1 & grid_y_axis_end = grid |> { 7 } 
    &
    homebase : NAT1 <-> NAT1 & homebase = { 1 |-> 1 }
    &   
    starbase : NAT1 <-> NAT1 & starbase = { 6 |-> 4 }
    &   
    asteroidsPos : NAT1 <-> NAT1 & asteroidsPos = 
    { 
        ( 3 |-> 2 ), 
        ( 3 |-> 5 ), 
        ( 5 |-> 4 ), 
        ( 6 |-> 7), 
        ( 7 |-> 1 ), 
        ( 7 |-> 5), 
        ( 7 |-> 7 ), 
        ( 8 |-> 3 ), 
        ( 10 |-> 6 ), 
        ( 11 |-> 2 ), 
        ( 12 |-> 5 ) 
    }
    &
    navPower : NAT1 & navPower = 5
    &
    warpDrivePower : NAT1 & warpDrivePower = 20
    &
    asteroidCrashedPower : NAT1 & asteroidCrashedPower = 10
    
VARIABLES
    x_axis_pos,
    
    y_axis_pos,
    
    spaceshipPower,
    
    spaceshipPath,
    numberOfCrashes
    

INVARIANT
    x_axis_pos : NAT1 & x_axis_pos : grid_x_axis
    &
    y_axis_pos : NAT1 & y_axis_pos : grid_y_axis
    &
    spaceshipPower : NAT
    &
    spaceshipPath : seq(NAT1 * NAT1)
    &
    numberOfCrashes : NAT
    
INITIALISATION
    x_axis_pos := 1 ||
    y_axis_pos := 1 ||
    spaceshipPower := 100 ||
    spaceshipPath := [] ||
    numberOfCrashes := 0

OPERATIONS
    report <-- spaceshipNavigation ( direction ) =
    PRE direction : NAVIGATION
    THEN
         //Move Up
        IF (direction = moveUp)
        THEN
            IF ( 
                    spaceshipPower >= navPower //has enough power to make the move
                    &
                    (x_axis_pos |-> y_axis_pos) /: grid_y_axis_end //Not at the end of the grid
                    &
                    (x_axis_pos |-> y_axis_pos + 1) /: asteroidsPos //New position is not occupied by an asteroid
    
                )
            THEN
                y_axis_pos := y_axis_pos + 1
                ||
                spaceshipPower := spaceshipPower - navPower
                ||
                spaceshipPath := spaceshipPath <- ( x_axis_pos |-> y_axis_pos )
                ||
                report := MOVE_UP_SUCCESS
                
            ELSIF  ( 
                        spaceshipPower < navPower 
                        or
                        (x_axis_pos |-> y_axis_pos) : grid_y_axis_end 
                        or
                        (x_axis_pos |-> y_axis_pos + 1) : asteroidsPos 
                    )
            THEN
                IF ( spaceshipPower < navPower )
                THEN
                    report:= CANNOT_MOVE__NOT_ENOUGH_POWER_AVAILABLE
                    
                ELSIF (x_axis_pos |-> y_axis_pos) : grid_y_axis_end 
                THEN
                    report := CANNOT_MOVE__OUT_OF_SPACE_BOUNDARY                                    
        
                ELSIF ( (x_axis_pos |-> y_axis_pos + 1) : asteroidsPos )
                THEN
                    report := CANNOT_MOVE__REGION_OCCUPIED_BY_AN_ASTEROID
                    ||
                    numberOfCrashes := numberOfCrashes + 1
                    ||
                    spaceshipPower := spaceshipPower - warpDrivePower
                END
            END
                            
        //Move Down        
        ELSIF (direction = moveDown)
        THEN
            IF ( 
                    spaceshipPower >= navPower 
                    &
                    (x_axis_pos |-> y_axis_pos) /: grid_y_axis_begin 
                    &
                    (x_axis_pos |-> y_axis_pos - 1) /: asteroidsPos 
                )
            THEN
                y_axis_pos := y_axis_pos - 1
                ||
                spaceshipPower := spaceshipPower - navPower
                ||
                spaceshipPath := spaceshipPath <- ( x_axis_pos |-> y_axis_pos )
                ||
                report := MOVE_DOWN_SUCCESS
            
            ELSIF  ( 
                        spaceshipPower < navPower
                        or
                        (x_axis_pos |-> y_axis_pos) : grid_y_axis_begin 
                        or
                        (x_axis_pos |-> y_axis_pos - 1) : asteroidsPos 
                    )
            THEN
                IF ( spaceshipPower < navPower )
                THEN
                    report:= CANNOT_MOVE__NOT_ENOUGH_POWER_AVAILABLE
                        
                ELSIF ( (x_axis_pos |-> y_axis_pos) : grid_y_axis_begin )
                THEN
                    report := CANNOT_MOVE__OUT_OF_SPACE_BOUNDARY
        
                ELSIF ( (x_axis_pos |-> y_axis_pos - 1) : asteroidsPos )
                THEN
                    report := CANNOT_MOVE__REGION_OCCUPIED_BY_AN_ASTEROID
                    ||
                    numberOfCrashes := numberOfCrashes
                    ||
                    spaceshipPower := spaceshipPower - warpDrivePower
                END
            END  
                            
            //Move Right(Forward)        
            ELSIF (direction = moveForward)
            THEN
                IF ( 
                        spaceshipPower >= navPower 
                        &
                        ( x_axis_pos |-> y_axis_pos ) /: grid_x_axis_end 
                        &
                        ( x_axis_pos + 1 |-> y_axis_pos ) /: asteroidsPos 
                    )
                THEN
                    x_axis_pos := x_axis_pos + 1
                    ||
                    spaceshipPower := spaceshipPower - navPower
                    ||
                    spaceshipPath := spaceshipPath <- ( x_axis_pos |-> y_axis_pos )
                    ||
                    report := MOVE_FORWARD_SUCCESS
                    
                ELSIF  ( 
                            spaceshipPower < navPower  
                            or
                            (x_axis_pos |-> y_axis_pos) : grid_x_axis_end 
                            or
                            (x_axis_pos + 1 |-> y_axis_pos) : asteroidsPos 
                        )
                THEN
                    IF ( spaceshipPower < navPower )
                    THEN
                        report:= CANNOT_MOVE__NOT_ENOUGH_POWER_AVAILABLE
                            
                    ELSIF ( (x_axis_pos |-> y_axis_pos) : grid_x_axis_end )
                    THEN
                        report := CANNOT_MOVE__OUT_OF_SPACE_BOUNDARY
            
                    ELSIF ( (x_axis_pos + 1 |-> y_axis_pos) : asteroidsPos )
                    THEN
                        report := CANNOT_MOVE__REGION_OCCUPIED_BY_AN_ASTEROID
                        ||
                        numberOfCrashes := numberOfCrashes
                        ||
                        spaceshipPower := spaceshipPower - warpDrivePower
    
                    END
                END
                    
                //Move Left(Backward)        
                ELSIF (direction = moveBackward)
                THEN
                    IF ( 
                            spaceshipPower >= navPower 
                            &
                            (x_axis_pos |-> y_axis_pos) /: grid_x_axis_begin 
                            &
                            (x_axis_pos - 1 |-> y_axis_pos) /: asteroidsPos 
                        )
                    THEN
                        x_axis_pos := x_axis_pos - 1
                        ||
                        spaceshipPower := spaceshipPower - navPower
                        ||
                        spaceshipPath := spaceshipPath <- ( x_axis_pos |-> y_axis_pos )
                        ||
                        report := MOVE_BACKWARD_SUCCESS
                        
                    ELSIF  ( 
                                spaceshipPower < navPower  
                                or
                                (x_axis_pos |-> y_axis_pos) : grid_x_axis_begin 
                                or
                                (x_axis_pos - 1 |-> y_axis_pos) : asteroidsPos 
                            )
                    THEN
                        IF ( spaceshipPower < navPower )
                        THEN
                            report:= CANNOT_MOVE__NOT_ENOUGH_POWER_AVAILABLE
                                
                        ELSIF ( (x_axis_pos |-> y_axis_pos) : grid_x_axis_begin )
                        THEN
                            report := CANNOT_MOVE__OUT_OF_SPACE_BOUNDARY
                
                        ELSIF ( (x_axis_pos - 1 |-> y_axis_pos) : asteroidsPos )
                        THEN
                            report := CANNOT_MOVE__REGION_OCCUPIED_BY_AN_ASTEROID
                            ||
                            numberOfCrashes := numberOfCrashes
                            ||
                            spaceshipPower := spaceshipPower - warpDrivePower
                        END
                    END  
                    
                END
    END ;
      

    
        //Warp-drive
    report <-- engageWarpDrive( new_x_axis, new_y_axis ) =
    PRE new_x_axis |-> new_y_axis : grid
    THEN
        IF 
            ( 
                spaceshipPower >= warpDrivePower
                &
                new_x_axis |-> new_y_axis /: asteroidsPos
            )
        THEN
            x_axis_pos := new_x_axis
            ||
            y_axis_pos := new_y_axis
            ||
            spaceshipPower := spaceshipPower - warpDrivePower
            ||
            spaceshipPath := spaceshipPath <- ( x_axis_pos |-> y_axis_pos )
            ||
            report := WARP_DRIVE_SUCCESS
            
        ELSIF 
            ( 
                spaceshipPower < warpDrivePower
                or
                new_x_axis |-> new_y_axis : asteroidsPos 
            )
        THEN
            IF ( spaceshipPower < warpDrivePower )
            THEN    
                report := CANNOT_ENGAGE_WARP_DRIVE__NOT_ENOUGH_POWER_AVAILABLE
                
            ELSIF ( new_x_axis |-> new_y_axis : asteroidsPos  )
            THEN
                report := CANNOT_ENGAGE_WARP_DRIVE__REGION_OCCUPIED_BY_AN_ASTEROID
                ||
                numberOfCrashes := numberOfCrashes
                ||
                spaceshipPower := spaceshipPower - warpDrivePower
            END
        END                
    END ;
    
    //Spaceship current position
    pos <-- getCurrentPos =
    BEGIN
        pos := x_axis_pos |-> y_axis_pos
    END ;
    
    //Mission route
    route <-- missionRoute =
    BEGIN
        route := spaceshipPath
    END ;
    
    //Mission status
    currentLocation, currentPower, asteroidCrashes <-- missionStatus = 
    BEGIN
        currentLocation := (x_axis_pos |-> y_axis_pos)
        ||
        currentPower := spaceshipPower
        ||
        asteroidCrashes := numberOfCrashes
    END ;
    
    //Spaceship docked?
    report <-- dockedAtStarbase =
    BEGIN
        IF ( x_axis_pos |-> y_axis_pos : starbase )
        THEN
            report := SPACESHIP_DOCKED
            
        ELSE
            report := SPACESHIP_NOT_DOCKED
        END
    END 
    
END




