cmake_minimum_required(VERSION 3.25)

project(vain)

include_directories(${CMAKE_SOURCE_DIR})
FILE(GLOB SRC ${CMAKE_SOURCE_DIR}/*.cpp)

find_package(ZLIB)
find_package(Threads REQUIRED)
find_package(OpenSSL REQUIRED)
find_package(Boost REQUIRED COMPONENTS system filesystem program_options date_time OPTIONAL_COMPONENTS atomic)

if(WIN32)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DWIN32_LEAN_AND_MEAN")
  add_executable("${PROJECT_NAME}" WIN32 ${SRC})
  list(APPEND MINGW_EXTRA "wsock32" "ws2_32" "iphlpapi")
  
  get_target_property(BOOSTFSLIBS Boost::filesystem INTERFACE_LINK_LIBRARIES)
  list(REMOVE_ITEM BOOSTFSLIBS synchronization)
  set_target_properties(Boost::filesystem PROPERTIES INTERFACE_LINK_LIBRARIES "${BOOSTFSLIBS}")  
endif()

target_link_libraries("${PROJECT_NAME}" ${Boost_LIBRARIES} OpenSSL::SSL OpenSSL::Crypto ZLIB::ZLIB Threads::Threads ${MINGW_EXTRA} ${CMAKE_REQUIRED_LIBRARIES})